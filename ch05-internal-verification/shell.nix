{ pkgs ? import <nixpkgs> {} }:

let
  pkg = pkgs.agda.mkDerivation(self: {
    name = "MyPackage";
    buildDepends = [
      pkgs.agdaIowaStdlib
      pkgs.AgdaStdlib (pkgs.haskellPackages.ghcWithPackages ( p: [p.ieee]) )
    ];
  });
in
  pkg.env
