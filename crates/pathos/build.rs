//! Reads CPC once, at build time: the state after reading the signature is
//! built into the binary as an image (`State::signature_image`), so that a
//! run of `pathos` starts from it instead of parsing the signature.

use std::path::PathBuf;

fn main() {
    let signature = "../../generated/cpc-checker/Cpc.cached.eo";
    println!("cargo::rerun-if-changed={signature}");
    println!("cargo::rerun-if-changed=build.rs");
    let input = std::fs::read(signature).expect("generated/cpc-checker/Cpc.cached.eo is read");
    let image =
        pathos_elab::State::signature_image(pathos_check::Options::default(), input, "Cpc.eo")
            .expect("pathos reads CPC");
    let out = PathBuf::from(std::env::var_os("OUT_DIR").expect("cargo sets OUT_DIR"));
    std::fs::write(out.join("cpc.image"), image).expect("the image is written");
}
