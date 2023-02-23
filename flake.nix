# nix flake init -t github:srid/haskell-flake
{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [ inputs.haskell-flake.flakeModule ];
      perSystem = { self', pkgs, ... }: {
        haskellProjects.default = {
          # packages.ling.root = ./.;  # This value is detected based on .cabal files
          # overrides = self: super: { };
          devShell = {
          #  enable = true;  # Enabled by default
            #tools = hp: { fourmolu = hp.fourmolu; ghcid = null; };
            tools = hp: { BNFC = hp.BNFC; };
          #  hlsCheck.enable = true;
          };
        };
        # haskell-flake doesn't set the default package, but you can do it here.
        packages.default = self'.packages.ling;
      };
    };
}
