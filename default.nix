{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7102" }:
let
  callPackage = nixpkgs.pkgs.haskell.packages.${compiler}.callPackage;
in
callPackage ./ling.nix {}
