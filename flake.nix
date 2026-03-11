{
  description = "Lean blueprint dev shell";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";

  outputs = { self, nixpkgs }:
  let
    systems = [
      "x86_64-linux"
      "aarch64-linux"
      "x86_64-darwin"
      "aarch64-darwin"
    ];
    mkShellFor = system:
      let
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
      };
  in
  {
    devShells = builtins.listToAttrs (map (system: {
      name = system;
      value = { default = mkShellFor system; };
    }) systems);
  };
}
