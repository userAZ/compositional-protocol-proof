{ system ? builtins.currentSystem }:

let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { inherit system; };
in
pkgs.mkShellNoCC {
  packages = [
    (pkgs.python313.withPackages (ps: with ps; [
      pandas
      great-tables
      rich
    ]))
  ];
}
