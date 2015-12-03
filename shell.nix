{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7102" }:

with nixpkgs.haskell.packages.${compiler};
let
  mkdocsInputs =
       [ nixpkgs.python27Full ] ++
       (with nixpkgs.python27Packages; [
        pip
        virtualenv
       ]);
  hfmt = callPackage ./nix/hfmt.nix {};
  BNFC = callPackage ./nix/BNFC.nix {};
in

nixpkgs.lib.overrideDerivation
  (import ./default.nix { inherit nixpkgs compiler; }).env
  (old:
   { buildInputs = old.buildInputs ++ mkdocsInputs ++ [
        cabal-install
        BNFC
        ghc-make
        ghc-mod
        hindent
        hfmt
        hlint
        stylish-haskell
        pointfree
        pointful
       ];})
