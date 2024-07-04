{
  description = "A modern SAT solver in Rust";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
  outputs = { self, nixpkgs }:
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
                   version = "0.18.0-dev1";
                   name = "splr-${version}";
                   pname = "splr";
                   src = self;
                   cargoHash = "sha256-7MY2o1aHJQ7ow5BbItQaDuc8vIQ68MqU2+aYuFVqK38=";
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
  };
}
