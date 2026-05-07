{
  description = "A modern SAT solver in Rust";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
  inputs.sat-bench.url = "github:shnarazk/SAT-bench";
  inputs.home.url = "github:shnarazk/flakes";

  outputs = { self, nixpkgs, sat-bench, home }:
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
                   cargoHash = "sha256-Mbd15EIej0903yh6LWUmegpfujZScKMXedqgNBjjM30=";
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
                  cargo-watch
                  drat-trim
                  home.packages.${system}.kissat
                  # nixpkgs.lldb_19
                  samply
                  tokei
                  sat-bench.packages.${system}.default
                  tinymist
                  typst
                ];
            };
          }
        )
      [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ]
    );
  };
}
