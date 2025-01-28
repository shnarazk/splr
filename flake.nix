{
  description = "A modern SAT solver in Rust";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
  inputs.sat-bench.url = "github:shnarazk/SAT-bench";
  outputs = { self, nixpkgs, sat-bench }:
  {
    packages = builtins.listToAttrs
      (map
        (system:
          with import nixpkgs { system = "${system}"; };
          {
            name = system;
            value = {
               default =
                 rustPlatform.buildRustPackage rec {
                   version = "0.17.4-20250128";
                   name = "splr-${version}";
                   pname = "splr";
                   src = self;
                   cargoHash = "sha256-VEnunp6Y7dZQZllNIaq3DYs3c5eTZ1qVy5ggNdNnFoM=";
                   buildInputs = rustc.buildInputs ++ lib.optional stdenv.isDarwin [ libiconv ];
                   buildPhase = "cargo build --release";
                   installPhase = ''
                     mkdir -p $out/bin;
                     install -t $out/bin target/release/splr target/release/dmcr
                   '';
                 };
            };
          }
        )
      [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ]
    );
    devShell = builtins.listToAttrs
      (map
        (system:
          with import nixpkgs { system = "${system}"; };
          {
            name = system;
            value = mkShell {
                packages = [
                  bashInteractive
                  samply
                  tokei
                  # cargo-watch
                  # nixpkgs.lldb_19
                  sat-bench.packages.${system}.default
                ];
            };
          }
        )
      [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ]
    );
  };
}
