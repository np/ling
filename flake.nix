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
      perSystem = { self', pkgs, ... }:
        let
          # NP: this is to support stack build within nix.
          # Inspired from https://docs.haskellstack.org/en/stable/nix_integration/
          # Wrap Stack to work with our Nix integration. We don't want to modify
          # stack.yaml so non-Nix users don't notice anything.
          # - no-nix: We don't want Stack's way of integrating Nix.
          # --system-ghc    # Use the existing GHC on PATH (will come from this Nix file)
          # --no-install-ghc  # Don't try to install GHC if no matching GHC found on PATH
          stack-wrapped = pkgs.symlinkJoin {
            name = "stack"; # will be available as the usual `stack` in terminal
            paths = [ pkgs.stack ];
            buildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/bin/stack \
                --add-flags "\
                  --nix \
                  --system-ghc \
                  --no-install-ghc \
                "
            '';
          };
        in {

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
              stack = stack-wrapped;
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
