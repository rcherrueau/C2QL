# https://nixos.org/nixpkgs/manual/#how-to-create-a-development-environment
{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7103" }:
let
  inherit (nixpkgs) pkgs;
  ghc = pkgs.haskell.packages.${compiler}.ghcWithPackages (ps: with ps; [
          cabal # idris
        ]);
in
pkgs.stdenv.mkDerivation {
  name = "my-idris-env";
  buildInputs = [ ghc ];
  shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
}
