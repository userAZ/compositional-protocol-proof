# Compositional Protocol Proof

We prove that for a class of MSI and RCC-family protocols, this class of
protocols compose together when used for separate core-clusters (cluster 
protocols) connected by a (global) protocol of the family in the level above,
with translation shims to translate requests between cluster and global
protcols.

## Artifact Evaluation Instructions

Load the compressed image into Docker.
```
docker load < cpp-lean-min-26.04-with-latest.tar.gz
```

Run the docker image interactively, with color:
```
docker run -it --name cpp-lean-min -e TERM=xterm-256color -p 8000:8000 cpp-lean:latest
```

In the directory "compositional-protocol-proof", please run:
```
git init
```
This is for leanblueprint to generate the webpage and pdf, if you want to view
the webpage and/or pdf.

Please check the pdf `Artifact-Instructions.pdf`. It contains instructions
on running the artifact evaluation. This README.md mainly has some
extra insturctions for viewing the `leanblueprint web` website, if
you're interested in viewing it.

### Extra Help for Running `leanblueprint web` Website, and Loading It

If you want to run `leanblueprint web`, you may need to run the following command first:
```
chmod +rw blueprint/web/js/svgxuse.js blueprint/web/js/jquery.min.js blueprint/web/js/plastex.js blueprint/web/styles/* blueprint/web/symbol-defs.svg
```

The docker image already includes the dependencies for `leanblueprint web` and
`leanblueprint pdf`; you do not need to run `nix-shell` inside Docker. If you
are using a source checkout outside Docker, use `nix-shell
leanblueprint-shell.nix` to load the leanblueprint dependencies.

Then build the webpage using `leanblueprint web`.

Then run `leanblueprint serve`.

Ensure you've run this docker image with port forwarding:
```
docker run -it --name cpp-lean-min -e TERM=xterm-256color -p 8000:8000 cpp-lean:latest
```

Then you can access the webpage from your local browser at
http://localhost:8000/
(even through the webpage is served from the docker container!).
