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
            tools = hp: {
              BNFC = hp.BNFC;
              stylish-haskell = hp.stylish-haskell;
              hlint = hp.hlint;
              ghc-make = hp.ghc-make;
              hindent = hp.hindent;
              pointfree = hp.pointfree;
              hpack = hp.hpack;
            # ghc-mod = hp.ghc-mod; => broken
            # hfmt = hp.hfmt; => broken
            # pointful = hp.pointful; => broken
            };
          #  hlsCheck.enable = true;
          };
        };
        # haskell-flake doesn't set the default package, but you can do it here.
        packages.default = self'.packages.ling;
      };
    };
}
