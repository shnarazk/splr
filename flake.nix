{
  description = "A modern SAT solver in Rust";
  inputs = {
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    nixpkgs.url = github:NixOS/nixpkgs;
  };
  outputs = { self, nixpkgs, crane }:
  {
    packages = builtins.listToAttrs
      (map
        (system:
          with import nixpkgs { system = "${system}"; };
          let
            craneLib = crane.lib.${system};
          in
            {
              name = system;
              value = {
                default = craneLib.buildPackage {
                  # name = "splr-${version}";
                  # pname = "splr";
                  # version = "0.17.2-20240204";
                  src = craneLib.cleanCargoSource (craneLib.path ./.);
                  buildInputs = [cargo rustc binutils ]
                   ++ lib.optional stdenv.isDarwin [ libiconv ];
                  doCheck = false;
                };
                devShells.default = craneLib.devShell {
                  inputsFrom = buildins.attrValues self.packages.${system};
                  nativeBuildInputs = [ clippy rust-analyzer rustfmt ];
                };
              };
            }
        )
      [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ]
    );
  };
}
