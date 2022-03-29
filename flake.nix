{
  description = "A modern SAT solver in Rust";
  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  outputs = { self, nixpkgs, flake-utils }:
  {
    packages = builtins.listToAttrs
      (map
        (system:
          with import nixpkgs { system = "${system}"; };
          {
            name = system;
            value = {
              default =
                stdenv.mkDerivation rec {
                  name = "splr-${version}";
                  pname = "splr";
                  version = "0.14.0-20220122";
                  src = self;
                  buildInputs = [ cargo rustc ];
                  buildPhase = "cargo build --release";
                  installPhase = ''
                    mkdir -p $out/bin
                    install -t $out/bin target/release/splr target/release/dmcr
                  '';
                };
            };
          })
      [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ]
    );
  };
}