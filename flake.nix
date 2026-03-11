{
  description = "Lean blueprint dev shell";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";

  outputs = { self, nixpkgs }:
  let
    system = builtins.currentSystem;
    pkgs = import nixpkgs { inherit system; };
  in
  {
    devShells.${system}.default = pkgs.mkShellNoCC {
      packages = with pkgs; [
        graphviz
        python312Packages.plastexdepgraph
        python312Packages.leanblueprint
        texliveFull
        texlivePackages.latexmk
      ];
    };
  };
}
