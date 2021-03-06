{
  description = "A modern SAT solver in Rust";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: {
      defaultPackage =
        with import nixpkgs { system = "${system}"; };
        stdenv.mkDerivation {
          name = "splr";
          src = self;
          buildInputs = [ cargo rustc ];
          buildPhase = "cargo build --release";
          installPhase = "mkdir -p $out/bin; install -t $out/bin target/release/splr target/release/dmcr";
        }
      ;
    })
  ;
}
