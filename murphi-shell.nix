{ system ? builtins.currentSystem }:

let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { inherit system; config = {}; overlays = []; };
in
pkgs.mkShellNoCC {
  packages = with pkgs; [
    # Murphi
    byacc
    bison
    flex
    # run *Gen
    python312Packages.colorama
    python312Packages.graphviz
    python312Packages.networkx
    python312Packages.psutil
    python312Packages.tabulate
    # antlr build
    python312Packages.build
    python312Packages.installer
    python312Packages.distutils
  ];

}
