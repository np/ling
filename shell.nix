{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7101" }:
nixpkgs.lib.overrideDerivation
  (import ./default.nix { inherit nixpkgs compiler; }).env
  (old:
   { buildInputs = old.buildInputs ++
       (with nixpkgs.haskell.packages.${compiler}; [
       cabal-install
       BNFC
      #ghcMod
    ]);})
