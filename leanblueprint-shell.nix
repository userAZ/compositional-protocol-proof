{ system ? builtins.currentSystem }:

let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { inherit system; };
in
pkgs.mkShellNoCC {
  packages = with pkgs; [
    graphviz
    python312Packages.plastexdepgraph
    python312Packages.leanblueprint
    texliveFull
    texlivePackages.latexmk
  ];
}
