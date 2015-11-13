{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7102" }:

let
  mkdocsInputs =
       [ nixpkgs.python27Full ] ++
       (with nixpkgs.python27Packages; [
        pip
        virtualenv
       ]);
  callPackage = nixpkgs.pkgs.haskell.packages.${compiler}.callPackage;
  hfmt = callPackage ./nix/hfmt.nix {};
in

nixpkgs.lib.overrideDerivation
  (import ./default.nix { inherit nixpkgs compiler; }).env
  (old:
   { buildInputs = old.buildInputs ++ mkdocsInputs ++
       (with nixpkgs.haskell.packages.${compiler}; [
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
       ]);})
