{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7102" }:

let mkdocsInputs =
       [ nixpkgs.python27Full ] ++
       (with nixpkgs.python27Packages; [
        pip
        virtualenv
       ]);
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
        hlint
        stylish-haskell
        pointfree
        pointful
       ]);})
