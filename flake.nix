{
  description = "tl";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        rust = rust-overlay.packages.${system}.rust;
      in
      {
        devShells.default = pkgs.mkShell
          {
            buildInputs = with pkgs; [
              rust
              rust-analyzer
              libiconv
              tree-sitter
              graphviz
            ];
          };
      });
}
