// #![no_std]
extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::ToTokens;

use syn::{parse_macro_input, spanned::Spanned, Ident, Meta};

/// The prefix used in field attributes: `#[concordium(attr = "something")]`
const CONCORDIUM_ATTRIBUTE: &str = "concordium";

/// A list of valid concordium field attributes
const VALID_CONCORDIUM_FIELD_ATTRIBUTES: [&str; 3] = ["size_length", "ensure_ordered", "rename"];

/// A list of valid concordium attributes
const VALID_CONCORDIUM_ATTRIBUTES: [&str; 2] = ["state_parameter", "bound"];

fn get_root() -> proc_macro2::TokenStream { quote!(concordium_std) }

/// A helper to report meaningful compilation errors
/// - If applied to an Ok value they simply return the underlying value.
/// - If applied to `Err(e)` then `e` is turned into a compiler error.
fn unwrap_or_report(v: syn::Result<TokenStream>) -> TokenStream {
    match v {
        Ok(ts) => ts,
        Err(e) => e.to_compile_error().into(),
    }
}

// Return whether a attribute item is present.
fn contains_attribute<'a, I: IntoIterator<Item = &'a Meta>>(iter: I, name: &str) -> bool {
    iter.into_iter().any(|attr| attr.path().is_ident(name))
}

/// Finds concordium field attributes.
fn get_concordium_field_attributes(attributes: &[syn::Attribute]) -> syn::Result<Vec<syn::Meta>> {
    get_concordium_attributes(attributes, true)
}

/// Finds concordium attributes, either field or general attributes.
fn get_concordium_attributes(
    attributes: &[syn::Attribute],
    for_field: bool,
) -> syn::Result<Vec<syn::Meta>> {
    let (valid_attributes, attribute_type) = if for_field {
        (&VALID_CONCORDIUM_FIELD_ATTRIBUTES[..], "concordium field attribute")
    } else {
        (&VALID_CONCORDIUM_ATTRIBUTES[..], "concordium attribute")
    };

    attributes
        .iter()
        // Keep only concordium attributes
        .flat_map(|attr| match attr.parse_meta() {
            Ok(syn::Meta::List(list)) if list.path.is_ident(CONCORDIUM_ATTRIBUTE) => {
                list.nested
            }
            _ => syn::punctuated::Punctuated::new(),
        })
        // Ensure only valid attributes and unwrap NestedMeta
        .map(|nested| match nested {
            syn::NestedMeta::Meta(meta) => {
                let path = meta.path();
                if valid_attributes.iter().any(|&attr| path.is_ident(attr)) {
                    Ok(meta)
                } else {
                    Err(syn::Error::new(meta.span(),
                        format!("The attribute '{}' is not supported as a {}.",
                        path.to_token_stream(), attribute_type)
                    ))
                }
            }
            lit => Err(syn::Error::new(lit.span(), format!("Literals are not supported in a {}.", attribute_type))),
        })
        .collect()
}

fn find_field_attribute_value(
    attributes: &[syn::Attribute],
    target_attr: &str,
) -> syn::Result<Option<syn::Lit>> {
    find_attribute_value(attributes, true, target_attr)
}

fn find_attribute_value(
    attributes: &[syn::Attribute],
    for_field: bool,
    target_attr: &str,
) -> syn::Result<Option<syn::Lit>> {
    let target_attr = format_ident!("{}", target_attr);
    let attr_values: Vec<_> = get_concordium_attributes(attributes, for_field)?
        .into_iter()
        .filter_map(|nested_meta| match nested_meta {
            syn::Meta::NameValue(value) if value.path.is_ident(&target_attr) => Some(value.lit),
            _ => None,
        })
        .collect();
    if attr_values.is_empty() {
        return Ok(None);
    }
    if attr_values.len() > 1 {
        let mut init_error = syn::Error::new(
            attr_values[1].span(),
            format!("Attribute '{}' should only be specified once.", target_attr),
        );
        for other in attr_values.iter().skip(2) {
            init_error.combine(syn::Error::new(
                other.span(),
                format!("Attribute '{}' should only be specified once.", target_attr),
            ))
        }
        Err(init_error)
    } else {
        Ok(Some(attr_values[0].clone()))
    }
}

fn find_length_attribute(attributes: &[syn::Attribute]) -> syn::Result<Option<u32>> {
    let value = match find_field_attribute_value(attributes, "size_length")? {
        Some(v) => v,
        None => return Ok(None),
    };

    // Save the span to be used in errors.
    let value_span = value.span();

    let value = match value {
        syn::Lit::Int(int) => int,
        _ => return Err(syn::Error::new(value_span, "Length attribute value must be an integer.")),
    };
    let value = match value.base10_parse() {
        Ok(v) => v,
        _ => {
            return Err(syn::Error::new(
                value_span,
                "Length attribute value must be a base 10 integer.",
            ))
        }
    };
    match value {
        1 | 2 | 4 | 8 => Ok(Some(value)),
        _ => Err(syn::Error::new(value_span, "Length info must be either 1, 2, 4, or 8.")),
    }
}

/// Find a 'state_parameter' attribute and return it as an identifier.
/// Checks that the attribute is only defined once and that the value is a
/// string.
fn find_state_parameter_attribute(
    attributes: &[syn::Attribute],
) -> syn::Result<Option<syn::TypePath>> {
    let value = match find_attribute_value(attributes, false, "state_parameter")? {
        Some(v) => v,
        None => return Ok(None),
    };

    match value {
        syn::Lit::Str(value) => Ok(Some(value.parse().map_err(|err| {
            syn::Error::new(err.span(), "state_parameter attribute value is not a valid type path")
        })?)),
        _ => Err(syn::Error::new(
            value.span(),
            "state_parameter attribute value must be a string which describes valid type path",
        )),
    }
}

/// The value of the bound attribute, e.g. "A: Serial, B: Deserial".
type BoundAttributeValue = syn::punctuated::Punctuated<syn::WherePredicate, syn::token::Comma>;

/// Bound attribute on some type.
#[derive(Debug)]
enum BoundAttribute {
    /// Represents a bound shared across all of the derived traits.
    /// E.g. the attribute: `bound = "A : Serial + Deserial"`
    Shared(BoundAttributeValue),
    /// Represents bounds explicitly set for each derived trait.
    /// E.g. the attribute: `bound(serial = "A : Serial", deserial = "A :
    /// Deserial")`
    Separate(SeparateBoundValue),
}

/// Represents bounds explicitly set for each derived trait.
///
/// E.g. `bound(serial = "A : Serial", deserial = "A : Deserial")`
#[derive(Debug)]
struct SeparateBoundValue {
    /// Bounds set for Deserial.
    deserial: Option<BoundAttributeValue>,
    /// Bounds set for Serial.
    serial:   Option<BoundAttributeValue>,
}

/// Concordium attributes supported on containers.
#[derive(Debug)]
struct ContainerAttributes {
    /// All of the `bound` attributes, either of the form `bound(serial = "..",
    /// deserial = "..")` or `bound = ".."`.
    bounds:          Vec<BoundAttribute>,
    /// The state parameter attribute. `state_parameter = ".."`
    state_parameter: Option<syn::TypePath>,
}

impl ContainerAttributes {
    /// Collect shared and explicit bounds set for the implementation of
    /// `Deserial`. `None` meaning no bound attributes are provided.
    fn deserial_bounds(&self) -> Option<BoundAttributeValue> {
        let mut bounds: Option<BoundAttributeValue> = None;
        for attribute in self.bounds.iter() {
            if let BoundAttribute::Shared(bound)
            | BoundAttribute::Separate(SeparateBoundValue {
                deserial: Some(bound),
                ..
            }) = attribute
            {
                bounds.get_or_insert(BoundAttributeValue::new()).extend(bound.clone());
            }
        }
        bounds
    }

    /// Collect shared and explicit bounds set for the implementation of
    /// `Serial`. `None` meaning no bound attributes are provided.
    fn serial_bounds(&self) -> Option<BoundAttributeValue> {
        let mut bounds: Option<BoundAttributeValue> = None;
        for attribute in self.bounds.iter() {
            if let BoundAttribute::Shared(bound)
            | BoundAttribute::Separate(SeparateBoundValue {
                serial: Some(bound),
                ..
            }) = attribute
            {
                bounds.get_or_insert(BoundAttributeValue::new()).extend(bound.clone());
            }
        }
        bounds
    }
}

impl TryFrom<&[syn::Attribute]> for ContainerAttributes {
    type Error = syn::Error;

    fn try_from(attributes: &[syn::Attribute]) -> Result<Self, Self::Error> {
        let metas = get_concordium_attributes(attributes, false)?;
        // Collect and combine all errors if any.
        let mut error_option: Option<syn::Error> = None;
        let mut bounds = Vec::new();
        for meta in metas.iter() {
            if meta.path().is_ident("bound") {
                match BoundAttribute::try_from(meta) {
                    Err(new_err) => match error_option.as_mut() {
                        Some(error) => error.combine(new_err),
                        None => error_option = Some(new_err),
                    },
                    Ok(bound) => bounds.push(bound),
                }
            }
        }

        if let Some(err) = error_option {
            Err(err)
        } else {
            Ok(ContainerAttributes {
                bounds,
                state_parameter: find_state_parameter_attribute(attributes)?,
            })
        }
    }
}

impl TryFrom<&syn::MetaList> for SeparateBoundValue {
    type Error = syn::Error;

    fn try_from(list: &syn::MetaList) -> Result<Self, Self::Error> {
        let items = &list.nested;
        if items.is_empty() {
            return Err(syn::Error::new(list.span(), "bound attribute cannot be empty"));
        }
        let mut deserial: Option<BoundAttributeValue> = None;
        let mut serial: Option<BoundAttributeValue> = None;

        for item in items {
            let syn::NestedMeta::Meta(nested_meta) = item else {
                        return Err(syn::Error::new(item.span(), "bound attribute list can only contain name value pairs"));
                    };
            let syn::Meta::NameValue(name_value) = nested_meta else {
                return Err(syn::Error::new(nested_meta.span(), "bound attribute list must contain named values"))
            };
            if name_value.path.is_ident("serial") {
                let syn::Lit::Str(lit_str) = &name_value.lit else {
                    return Err(syn::Error::new(name_value.lit.span(), "bound attribute must be a string literal"))
                };
                let value = lit_str.parse_with(BoundAttributeValue::parse_terminated)?;
                if let Some(serial_value) = serial.as_mut() {
                    serial_value.extend(value)
                } else {
                    serial = Some(value);
                };
            } else if name_value.path.is_ident("deserial") {
                let syn::Lit::Str(lit_str) = &name_value.lit else {
                            return Err(syn::Error::new(name_value.lit.span(), "bound attribute must be a string literal"))
                        };
                let value = lit_str.parse_with(BoundAttributeValue::parse_terminated)?;
                if let Some(deserial_value) = deserial.as_mut() {
                    deserial_value.extend(value)
                } else {
                    deserial = Some(value);
                };
            } else if name_value.path.is_ident("schema_type") {
                continue;
            } else {
                return Err(syn::Error::new(
                    item.span(),
                    "bound attribute list only allow the keys 'serial' and 'deserial'",
                ));
            }
        }

        Ok(Self {
            deserial,
            serial,
        })
    }
}

impl TryFrom<&syn::Meta> for BoundAttribute {
    type Error = syn::Error;

    fn try_from(meta: &syn::Meta) -> Result<Self, Self::Error> {
        match meta {
            syn::Meta::List(list) => {
                Ok(BoundAttribute::Separate(SeparateBoundValue::try_from(list)?))
            }
            syn::Meta::NameValue(name_value) => {
                let syn::Lit::Str(ref lit_str) = name_value.lit else {
                    return Err(syn::Error::new(name_value.lit.span(), "bound attribute must be a string literal"))
                };

                let value = lit_str.parse_with(BoundAttributeValue::parse_terminated)?;
                Ok(BoundAttribute::Shared(value))
            }
            syn::Meta::Path(_) => {
                Err(syn::Error::new(meta.span(), "bound attribute value is invalid"))
            }
        }
    }
}

fn impl_deserial_field(
    f: &syn::Field,
    ident: &syn::Ident,
    source: &syn::Ident,
) -> syn::Result<proc_macro2::TokenStream> {
    let concordium_attributes = get_concordium_field_attributes(&f.attrs)?;
    let ensure_ordered = contains_attribute(&concordium_attributes, "ensure_ordered");
    let size_length = find_length_attribute(&f.attrs)?;
    let has_ctx = ensure_ordered || size_length.is_some();
    let ty = &f.ty;
    let root = get_root();

    if has_ctx {
        // Default size length is u32, i.e. 4 bytes.
        let l = format_ident!("U{}", 8 * size_length.unwrap_or(4));

        Ok(quote! {
            let #ident = <#ty as #root::DeserialCtx>::deserial_ctx(#root::schema::SizeLength::#l, #ensure_ordered, #source)?;
        })
    } else {
        Ok(quote! {
            let #ident = <#ty as #root::Deserial>::deserial(#source)?;
        })
    }
}

/// Derive the Deserial trait. See the documentation of
/// [`derive(Serial)`](./derive.Serial.html) for details and limitations.
///
/// In addition to the attributes supported by
/// [`derive(Serial)`](./derive.Serial.html), this derivation macro supports the
/// `ensure_ordered` attribute. If applied to a field the of type `BTreeMap` or
/// `BTreeSet` deserialization will additionally ensure that the keys are in
/// strictly increasing order. By default deserialization only ensures
/// uniqueness.
///
/// # Example
/// ``` ignore
/// #[derive(Deserial)]
/// struct Foo {
///     #[concordium(size_length = 1, ensure_ordered)]
///     bar: BTreeSet<u8>,
/// }
/// ```
#[proc_macro_derive(Deserial, attributes(concordium))]
pub fn deserial_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    unwrap_or_report(impl_deserial(&ast))
}

fn impl_deserial(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let data_name = &ast.ident;

    let span = ast.span();

    let read_ident = format_ident!("__R", span = span);

    let source_ident = Ident::new("________________source", Span::call_site());
    let root = get_root();

    let body_tokens = match ast.data {
        syn::Data::Struct(ref data) => {
            let mut names = proc_macro2::TokenStream::new();
            let mut field_tokens = proc_macro2::TokenStream::new();
            let return_tokens = match data.fields {
                syn::Fields::Named(_) => {
                    for field in data.fields.iter() {
                        let field_ident = field.ident.clone().unwrap(); // safe since named fields.
                        field_tokens.extend(impl_deserial_field(
                            field,
                            &field_ident,
                            &source_ident,
                        ));
                        names.extend(quote!(#field_ident,))
                    }
                    quote!(Ok(#data_name{#names}))
                }
                syn::Fields::Unnamed(_) => {
                    for (i, f) in data.fields.iter().enumerate() {
                        let field_ident = format_ident!("x_{}", i);
                        field_tokens.extend(impl_deserial_field(f, &field_ident, &source_ident));
                        names.extend(quote!(#field_ident,))
                    }
                    quote!(Ok(#data_name(#names)))
                }
                _ => quote!(Ok(#data_name{})),
            };
            quote! {
                #field_tokens
                #return_tokens
            }
        }
        syn::Data::Enum(ref data) => {
            let mut matches_tokens = proc_macro2::TokenStream::new();
            let source = Ident::new("________________source", Span::call_site());
            let size = if data.variants.len() <= 256 {
                format_ident!("u8")
            } else if data.variants.len() <= 256 * 256 {
                format_ident!("u16")
            } else {
                return Err(syn::Error::new(
                    ast.span(),
                    "[derive(Deserial)]: Too many variants. Maximum 65536 are supported.",
                ));
            };
            for (i, variant) in data.variants.iter().enumerate() {
                let (field_names, pattern) = match variant.fields {
                    syn::Fields::Named(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|field| field.ident.clone().unwrap())
                            .collect();
                        (field_names.clone(), quote! { {#(#field_names),*} })
                    }
                    syn::Fields::Unnamed(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, _)| format_ident!("x_{}", i))
                            .collect();
                        (field_names.clone(), quote! { ( #(#field_names),* ) })
                    }
                    syn::Fields::Unit => (Vec::new(), proc_macro2::TokenStream::new()),
                };

                let field_tokens: proc_macro2::TokenStream = field_names
                    .iter()
                    .zip(variant.fields.iter())
                    .map(|(name, field)| impl_deserial_field(field, name, &source))
                    .collect::<syn::Result<proc_macro2::TokenStream>>()?;
                let idx_lit = syn::LitInt::new(i.to_string().as_str(), Span::call_site());
                let variant_ident = &variant.ident;
                matches_tokens.extend(quote! {
                    #idx_lit => {
                        #field_tokens
                        Ok(#data_name::#variant_ident #pattern)
                    },
                })
            }
            quote! {
                let idx = <#size as #root::Deserial>::deserial(#source)?;
                match idx {
                    #matches_tokens
                    _ => Err(Default::default())
                }
            }
        }
        _ => unimplemented!("#[derive(Deserial)] is not implemented for union."),
    };

    let container_attributes = ContainerAttributes::try_from(ast.attrs.as_slice())?;
    let (impl_generics, ty_generics, where_clauses) = ast.generics.split_for_impl();

    let where_clauses_tokens =
        if let Some(attribute_bounds) = container_attributes.deserial_bounds() {
            attribute_bounds.into_token_stream()
        } else {
            // Extend where clauses with Deserial predicate of each generic.
            let where_clause_deserial: proc_macro2::TokenStream = ast
                .generics
                .type_params()
                .map(|type_param| {
                    let type_param_ident = &type_param.ident;
                    quote! (#type_param_ident: #root::Deserial,)
                })
                .collect();

            if let Some(where_clauses) = where_clauses {
                let predicates = &where_clauses.predicates;
                quote!(#predicates, where_clause_deserial)
            } else {
                where_clause_deserial
            }
        };

    let gen = quote! {
        #[automatically_derived]
        impl #impl_generics #root::Deserial for #data_name #ty_generics where #where_clauses_tokens {
            fn deserial<#read_ident: #root::Read>(#source_ident: &mut #read_ident) -> #root::ParseResult<Self> {
                #body_tokens
            }
        }
    };
    Ok(gen.into())
}

/// Derive the [`Serial`] trait for the type.
///
/// If the type is a struct all fields must implement the [`Serial`] trait. If
/// the type is an enum then all fields of each of the enums must implement the
/// [`Serial`] trait.
///
/// Fields of structs are serialized in the order they appear in the code.
///
/// Enums can have no more than 65536 variants. They are serialized by using a
/// tag to indicate the variant, enumerating them in the order they are written
/// in source code. If the number of variants is less than or equal 256 then a
/// single byte is used to encode it. Otherwise two bytes are used for the tag,
/// encoded in little endian.
///
/// ## Generic type bounds
///
/// By default a trait bound is added on each generic type for implementing
/// [`Serial`]. However, if this is not desirable, the bound can be put
/// explicitly using the `bound` attribute on the type overriding the default
/// behavior.
///
/// ### Example
/// ```ignore
/// #[derive(Serial)]
/// #[concordium(bound(serial = "A: SomeOtherTrait"))]
/// struct Foo<A> {
///     bar: A,
/// }
/// ```
///
/// ## Collections
///
/// Collections (Vec, BTreeMap, BTreeSet) and strings (String, str) are by
/// default serialized by prepending the number of elements as 4 bytes
/// little-endian. If this is too much or too little, fields of the above types
/// can be annotated with `size_length`.
///
/// The value of this field is the number of bytes that will be used for
/// encoding the number of elements. Supported values are `1,` `2,` `4,` `8`.
///
/// For BTreeMap and BTreeSet the serialize method will serialize values in
/// increasing order of keys.
///
/// ### Example
/// ```ignore
/// #[derive(Serial)]
/// struct Foo {
///     #[concordium(size_length = 1)]
///     bar: BTreeSet<u8>,
/// }
/// ```
#[proc_macro_derive(Serial, attributes(concordium))]
pub fn serial_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    unwrap_or_report(impl_serial(&ast))
}

fn impl_serial_field(
    field: &syn::Field,
    ident: &proc_macro2::TokenStream,
    out: &syn::Ident,
) -> syn::Result<proc_macro2::TokenStream> {
    let root = get_root();

    if let Some(size_length) = find_length_attribute(&field.attrs)? {
        let l = format_ident!("U{}", 8 * size_length);
        Ok(quote!({
            #root::SerialCtx::serial_ctx(#ident, #root::schema::SizeLength::#l, #out)?;
        }))
    } else {
        Ok(quote! {
            #root::Serial::serial(#ident, #out)?;
        })
    }
}

fn impl_serial(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let data_name = &ast.ident;

    let span = ast.span();

    let write_ident = format_ident!("W", span = span);

    let out_ident = format_ident!("out");
    let root = get_root();

    let body = match ast.data {
        syn::Data::Struct(ref data) => {
            let fields_tokens = match data.fields {
                syn::Fields::Named(_) => {
                    data.fields
                        .iter()
                        .map(|field| {
                            let field_ident = field.ident.clone().unwrap(); // safe since named fields.
                            let field_ident = quote!(&self.#field_ident);
                            impl_serial_field(field, &field_ident, &out_ident)
                        })
                        .collect::<syn::Result<_>>()?
                }
                syn::Fields::Unnamed(_) => data
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        let i = syn::LitInt::new(i.to_string().as_str(), Span::call_site());
                        let field_ident = quote!(&self.#i);
                        impl_serial_field(field, &field_ident, &out_ident)
                    })
                    .collect::<syn::Result<_>>()?,
                syn::Fields::Unit => proc_macro2::TokenStream::new(),
            };
            quote! {
                #fields_tokens
                Ok(())
            }
        }
        syn::Data::Enum(ref data) => {
            let mut matches_tokens = proc_macro2::TokenStream::new();

            let size = if data.variants.len() <= 256 {
                format_ident!("u8")
            } else if data.variants.len() <= 256 * 256 {
                format_ident!("u16")
            } else {
                unimplemented!(
                    "[derive(Serial)]: Enums with more than 65536 variants are not supported."
                );
            };

            for (i, variant) in data.variants.iter().enumerate() {
                let (field_names, pattern) = match variant.fields {
                    syn::Fields::Named(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|field| field.ident.clone().unwrap())
                            .collect();
                        (field_names.clone(), quote! { {#(#field_names),*} })
                    }
                    syn::Fields::Unnamed(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, _)| format_ident!("x_{}", i))
                            .collect();
                        (field_names.clone(), quote! { (#(#field_names),*) })
                    }
                    syn::Fields::Unit => (Vec::new(), proc_macro2::TokenStream::new()),
                };
                let field_tokens: proc_macro2::TokenStream = field_names
                    .iter()
                    .zip(variant.fields.iter())
                    .map(|(name, field)| impl_serial_field(field, &quote!(#name), &out_ident))
                    .collect::<syn::Result<_>>()?;

                let idx_lit =
                    syn::LitInt::new(format!("{}{}", i, size).as_str(), Span::call_site());
                let variant_ident = &variant.ident;

                matches_tokens.extend(quote! {
                    #data_name::#variant_ident #pattern => {
                        #root::Serial::serial(&#idx_lit, #out_ident)?;
                        #field_tokens
                    },
                })
            }
            quote! {
                match self {
                    #matches_tokens
                }
                Ok(())
            }
        }
        _ => unimplemented!("#[derive(Serial)] is not implemented for union."),
    };

    let container_attributes = ContainerAttributes::try_from(ast.attrs.as_slice())?;
    let (impl_generics, ty_generics, where_clauses) = ast.generics.split_for_impl();

    let where_clauses_tokens = if let Some(attribute_bounds) = container_attributes.serial_bounds()
    {
        attribute_bounds.into_token_stream()
    } else {
        let state_parameter_ident = container_attributes
            .state_parameter
            .as_ref()
            .and_then(|type_path| type_path.path.get_ident());
        // Extend where clauses with Serial predicate of each generic.
        let where_clause_serial: proc_macro2::TokenStream = ast
            .generics
            .type_params()
            .filter_map(|type_param| {
                match state_parameter_ident {
                    // Skip adding the predicate for the state_parameter.
                    Some(state_parameter) if state_parameter == &type_param.ident => None,
                    _ => {
                        let type_param_ident = &type_param.ident;
                        Some(quote! (#type_param_ident: #root::Serial,))
                    }
                }
            })
            .collect();

        if let Some(where_clauses) = where_clauses {
            let predicates = &where_clauses.predicates;
            quote!(#predicates, where_clause_serial)
        } else {
            where_clause_serial
        }
    };

    let gen = quote! {
        #[automatically_derived]
        impl #impl_generics #root::Serial for #data_name #ty_generics where #where_clauses_tokens {
            fn serial<#write_ident: #root::Write>(&self, #out_ident: &mut #write_ident) -> Result<(), #write_ident::Err> {
                #body
            }
        }
    };
    Ok(gen.into())
}

/// A helper macro to derive both the Serial and Deserial traits.
/// `[derive(Serialize)]` is equivalent to `[derive(Serial, Deserial)]`, see
/// documentation of the latter two for details and options:
/// [`derive(Serial)`](./derive.Serial.html),
/// [`derive(Deserial)`](./derive.Deserial.html).
#[proc_macro_derive(Serialize, attributes(concordium))]
pub fn serialize_derive(input: TokenStream) -> TokenStream {
    unwrap_or_report(serialize_derive_worker(input))
}

fn serialize_derive_worker(input: TokenStream) -> syn::Result<TokenStream> {
    let ast = syn::parse(input)?;
    let mut tokens = impl_deserial(&ast)?;
    tokens.extend(impl_serial(&ast)?);
    Ok(tokens)
}

#[cfg(test)]
mod test {
    use super::*;

    /// Test parsing for bound attribute when using syntax for sharing.
    #[test]
    fn test_parse_shared_bounds() {
        let ast: syn::ItemStruct = syn::parse_quote! {
            #[concordium(bound = "T: B")]
            struct MyStruct{}
        };

        let parsed = ContainerAttributes::try_from(ast.attrs.as_slice())
            .expect("Failed to parse container attributes");

        assert!(parsed.deserial_bounds().is_some(), "Failed to add shared bound");
        assert!(parsed.serial_bounds().is_some(), "Failed to add shared bound");
    }

    /// Test parsing for bound attribute when using syntax for Deserial
    /// explicit.
    #[test]
    fn test_parse_deserial_explicit_bounds() {
        let ast: syn::ItemStruct = syn::parse_quote! {
            #[concordium(bound(deserial  = "T: B"))]
            struct MyStruct{}
        };

        let parsed = ContainerAttributes::try_from(ast.attrs.as_slice())
            .expect("Failed to parse container attributes");

        assert!(parsed.deserial_bounds().is_some(), "Failed to add explicit bound");
        assert!(parsed.serial_bounds().is_none(), "Unexpected bound added for Serial");
    }

    /// Test parsing for bound attribute when using syntax for Serial explicit.
    #[test]
    fn test_parse_serial_explicit_bounds() {
        let ast: syn::ItemStruct = syn::parse_quote! {
            #[concordium(bound(serial  = "T: B"))]
            struct MyStruct{}
        };

        let parsed = ContainerAttributes::try_from(ast.attrs.as_slice())
            .expect("Failed to parse container attributes");

        assert!(parsed.serial_bounds().is_some(), "Failed to add explicit bound");
        assert!(parsed.deserial_bounds().is_none(), "Unexpected bound added for Deserial");
    }

    /// Test parsing for bound attribute when using syntax for SchemaType
    /// explicit.
    #[test]
    fn test_parse_schema_type_explicit_bounds() {
        let ast: syn::ItemStruct = syn::parse_quote! {
            #[concordium(bound(schema_type  = "T: B"))]
            struct MyStruct{}
        };

        let parsed = ContainerAttributes::try_from(ast.attrs.as_slice())
            .expect("Failed to parse container attributes");

        assert!(parsed.deserial_bounds().is_none(), "Unexpected bound added for Deserial");
        assert!(parsed.serial_bounds().is_none(), "Unexpected bound added for Serial");
    }
}
