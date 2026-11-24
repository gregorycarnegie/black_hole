fn main() {
    #[cfg(feature = "optix")]
    optix_bindings();
}

/// Generates OptiX bindings into OUT_DIR. The SDK licence allows building against
/// its headers but not redistributing them, so nothing generated is committed.
#[cfg(feature = "optix")]
fn optix_bindings() {
    println!("cargo:rerun-if-env-changed=OPTIX_ROOT");
    let root = std::env::var("OPTIX_ROOT")
        .expect("set OPTIX_ROOT to the OptiX SDK folder that contains include/optix.h");
    let include = std::path::Path::new(&root).join("include");
    let bindings = bindgen::Builder::default()
        .header_contents(
            "wrapper.h",
            "typedef struct CUctx_st *CUcontext;\n\
             typedef struct CUstream_st *CUstream;\n\
             #define OPTIX_DONT_INCLUDE_CUDA\n\
             #include <optix_function_table.h>\n",
        )
        .clang_arg(format!("-I{}", include.display()))
        .allowlist_type("Optix.*")
        .allowlist_var("OPTIX_.*")
        .derive_default(true)
        .generate()
        .expect("generate OptiX bindings");
    let out = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("optix.rs");
    bindings.write_to_file(out).expect("write OptiX bindings");
}
