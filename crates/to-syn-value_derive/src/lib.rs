use syn::*;
use quote::*;

#[proc_macro_derive(ToDeriveInput)]
pub fn derive_to_derive_input(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derive_input = parse_macro_input!(input as DeriveInput);
    let ty_name = derive_input.ident.clone();

    quote! {
        use to_syn_value::*;

        impl ToDeriveInput for #ty_name {
            fn to_derive_input() -> syn::DeriveInput {
                syn::parse_quote! {
                    #derive_input
                }
            }
        }
    }.into()
}
