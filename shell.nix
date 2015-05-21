{ pkgs ? import <nixpkgs> {} }:
let haskellPackages =
      pkgs.recurseIntoAttrs
        (pkgs.haskellPackages.override {
           extension = self: super:
                       {
                         BNFC = self.callPackage ./nix/BNFC.nix {};
                         thisPackage = haskellPackages.callPackage (import ./default.nix) {};
                       };
         });
in pkgs.lib.overrideDerivation haskellPackages.thisPackage (old: {
   buildInputs = old.buildInputs ++ [
     haskellPackages.cabalInstall
     haskellPackages.BNFC
#     haskellPackages.ghcMod
     # (2)
   ];})
