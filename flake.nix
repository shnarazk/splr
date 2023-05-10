{
  description = "A modern SAT solver in Rust";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs;
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages."${system}";
    in {
      devShell = pkgs.mkShell {
        nativeBuildInputs = with pkgs; [rustup];
      };
      packages = let
        callPackage = pkgs.callPackage;
      in {
        default = callPackage ({
          rustPlatform,
          lib,
        }:
          rustPlatform.buildRustPackage {
            pname = "splr";
            version = "0.17.0-git";

            src = lib.cleanSource self;

            cargoSha256 = "sha256-tz5ow4p07RV5P0I/w5s2zKOYzV+YHsnVNCchMZSLLGE=";

            meta = {
              description = "A modern SAT solver in Rust";
              homepage = "https://github.com/shnarazk/splr";
              license = with lib.licenses; [mpl20];
            };
          }) {};
      };
    });
}
