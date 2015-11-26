{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7102" }:
let
  callPackage = nixpkgs.pkgs.haskell.packages.${compiler}.callPackage;
  # reflection = callPackage ./nix/reflection.nix {};
  # lens = callPackage ./nix/lens.nix { inherit (reflection); };
in
callPackage ./ling.nix { inherit (lens); }
