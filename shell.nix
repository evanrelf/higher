let
  pkgs = import <nixpkgs> { };

in
pkgs.mkShell {
  packages = [
    pkgs.cabal-install
    pkgs.ghc
    pkgs.ghcid
  ];
}
