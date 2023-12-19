use crate::{
    common::*,
    rewriter,
    specifications::{
        common::{generate_struct_name, SpecificationId},
        preparser::{parse_owns, parse_prusti, ParsedOwns},
    },
    SPECS_VERSION,
};
use proc_macro2::{Span, TokenStream};
use quote::quote_spanned;
use syn::{parse_quote_spanned, spanned::Spanned};

pub fn rewrite_impl(
    item_impl: &syn::ItemImpl,
    owns_attr: &TokenStream,
) -> syn::Result<TokenStream> {
    let rewritten = rewrite_impl_internal(item_impl, owns_attr)?;

    let new_struct = rewritten.generated_struct;
    let new_impl = rewritten.generated_impl;
    Ok(quote_spanned! {item_impl.span()=>
        #[prusti::specs_version = #SPECS_VERSION]
        #new_struct
        #new_impl

    })
}

struct RewrittenOwns {
    generated_struct: syn::ItemStruct,
    generated_impl: syn::ItemImpl,
}

fn rewrite_impl_internal(
    item_impl: &syn::ItemImpl,
    owns_attr: &TokenStream,
) -> syn::Result<RewrittenOwns> {
    if !item_impl.items.is_empty() {
        return Err(syn::Error::new(
            Span::call_site(),
            "#[capable(..)] can only be applied to implementations with no items",
        ));
    }
    if item_impl.trait_.is_some() {
        return Err(syn::Error::new(
            Span::call_site(),
            "#[capable(..)] cannot be applied to trait implementations",
        ));
    }

    let new_struct = generate_new_struct(item_impl)?;
    let struct_ident = &new_struct.ident;
    let generic_args = strip_generics_bounds(&new_struct.generics);
    let struct_ty: syn::Type = parse_quote_spanned! {item_impl.span()=>
        #struct_ident #generic_args
    };

    // Prepare the new impl
    let mut new_impl = item_impl.clone();
    let mut self_ty = new_impl.self_ty;
    new_impl.self_ty = box struct_ty;

    // Remove <..> from the path of the specified Self type
    if let syn::Type::Path(type_path) = self_ty.as_mut() {
        for seg in type_path.path.segments.iter_mut() {
            if let syn::PathArguments::AngleBracketed(genargs) = &mut seg.arguments {
                genargs.colon2_token = Some(<syn::Token![::]>::default());
            }
        }
    }

    // Parse the attributes and convert them to spec methods
    let parsed_owns = parse_owns(owns_attr.clone())?;
    let spec_items = generate_spec_items(parsed_owns, &self_ty)?;
    new_impl.items = spec_items.into_iter().map(syn::ImplItem::Method).collect();

    Ok(RewrittenOwns {
        generated_struct: new_struct,
        generated_impl: new_impl,
    })
}

fn generate_new_struct(item_impl: &syn::ItemImpl) -> syn::Result<syn::ItemStruct> {
    let struct_name = generate_struct_name(item_impl);
    let struct_ident = syn::Ident::new(&struct_name, item_impl.span());

    let mut new_struct: syn::ItemStruct = parse_quote_spanned! {item_impl.span()=>
        #[allow(non_camel_case_types)] struct #struct_ident;
    };
    new_struct.generics = item_impl.generics.clone();

    add_phantom_data_for_generic_params(&mut new_struct);
    Ok(new_struct)
}

fn generate_spec_items(
    parsed_owns: ParsedOwns,
    self_ty: &syn::Type,
) -> syn::Result<Vec<syn::ImplItemMethod>> {
    let mut spec_items = vec![];
    let mut rewriter = rewriter::AstRewriter::new();
    let mut opt_condition_spec_id: Option<SpecificationId> = None;

    if !parsed_owns.condition.is_empty() {
        opt_condition_spec_id = Some(rewriter.generate_spec_id());
        let condition_spec_id_str = opt_condition_spec_id.unwrap().to_string();
        let condition_span = parsed_owns.condition.span();
        let body = parse_prusti(parsed_owns.condition)?;
        let mut condition_item: syn::ImplItemMethod = parse_quote_spanned! { condition_span =>
            #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case)]
            #[prusti::spec_only]
            #[prusti::spec_id = #condition_spec_id_str]
            fn prusti_owns_condition(_self: #self_ty) -> bool {
                #body
            }
        };
        condition_item.rewrite_self_type(self_ty, None);
        condition_item.rewrite_receiver(self_ty);
        condition_item.rewrite_self_type(self_ty, None);
        condition_item.rewrite_receiver(self_ty);
        spec_items.push(condition_item);
    }

    let self_ownership = parsed_owns.self_ownership.to_string();
    let target_ownership = parsed_owns.target_ownership.to_string();
    let target_spec_id = rewriter.generate_spec_id();
    let target_spec_id_str = target_spec_id.to_string();
    let target_parent_spec_id = rewriter.generate_spec_id();
    let target_parent_spec_id_str = target_parent_spec_id.to_string();
    let target_span = parsed_owns.target.span();
    let body = parse_prusti(parsed_owns.target)?;
    let mut target_expr_item: syn::ExprClosure = parse_quote_spanned! { target_span =>
        |_self: #self_ty| -> _ { #body as *const _ }
    };
    target_expr_item.attrs.extend([
        parse_quote_spanned! { target_span => #[prusti::spec_only] },
        parse_quote_spanned! { target_span => #[prusti::ownership_spec] },
        parse_quote_spanned! { target_span => #[prusti::spec_id = #target_spec_id_str] },
        parse_quote_spanned! { target_span => #[prusti::self_ownership = #self_ownership] },
        parse_quote_spanned! { target_span => #[prusti::target_ownership = #target_ownership] },
        parse_quote_spanned! { target_span => #[prusti::target_parent_spec_id = #target_parent_spec_id_str] },
    ]);
    if let Some(spec_id) = opt_condition_spec_id {
        let spec_id_str = spec_id.to_string();
        target_expr_item
            .attrs
            .push(parse_quote_spanned! { target_span =>
                #[prusti::condition_spec_id = #spec_id_str]
            });
    };
    let mut target_item: syn::ImplItemMethod = parse_quote_spanned! { target_span =>
        #[allow(unused_must_use, unused_parens, unused_variables, dead_code, non_snake_case)]
        #[prusti::spec_only]
        #[prusti::spec_id = #target_parent_spec_id_str]
        fn prusti_owns_target() {
            #target_expr_item;
        }
    };
    target_item.rewrite_self_type(self_ty, None);
    target_item.rewrite_receiver(self_ty);
    spec_items.push(target_item);

    Ok(spec_items)
}
