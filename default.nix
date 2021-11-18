{ sources ? import ./nix
}:
let
  pkgs = sources.nixpkgs {};
  gitignore = sources.gitignore{ lib = pkgs.lib; };
in
  pkgs.stdenv.mkDerivation {
    name = "sizeof";

    src = builtins.path {
      name = "sizeof";
      path = ./.;
      filter = gitignore.gitignoreFilter ./.;
    };

    buildInputs = with pkgs; [
      ghc
      cabal-install
      hlint
    ];
  }
