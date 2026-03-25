{ system ? builtins.currentSystem }:

let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-unstable";
  pkgs = import nixpkgs {
    inherit system;
    overlays = [
      (self: super: {
        python312Packages = super.python312Packages // {
          plastexshowmore = super.python312Packages.plastexshowmore.overridePythonAttrs (_: {
            version = "0.0.2";
            src = self.fetchPypi {
              pname = "plastexshowmore";
              version = "0.0.2";
              sha256 = "f1fea7225eae7e2bd3f91235c36c9231087e3793593c8c139c3955cd008f0b51";
            };
          });
          leanblueprint = super.python312Packages.leanblueprint.overridePythonAttrs (old: {
            pythonRelaxDeps = (old.pythonRelaxDeps or []) ++ [ "plastexshowmore" ];
            nativeBuildInputs = (old.nativeBuildInputs or []) ++ [ self.python312Packages.pythonRelaxDepsHook ];
          });
        };
      })
    ];
  };
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
