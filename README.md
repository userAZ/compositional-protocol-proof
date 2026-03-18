# Compositional Protocol Proof

We prove that for a class of MSI and RCC-family protocols, this class of
protocols compose together when used for separate core-clusters (cluster 
protocols) connected by a (global) protocol of the family in the level above,
with translation shims to translate requests between cluster and global
protcols.

## Artifact Evaluation Instructions

Please check the pdf `Instructions.pdf`. It contains instructions
on running the artifact evaluation.

### Extra Help for Running `leanblueprint web` Website, and Loading It

If you want to run `leanblueprint web`, you may need to run the following command first:
```
chmod +rw blueprint/web/js/svgxuse.js blueprint/web/js/jquery.min.js blueprint/web/js/plastex.js blueprint/web/styles/* blueprint/web/symbol-defs.svg
```

Remember to run `nix-shell leanblueprint-shell.nix` to load the dependencies for leanblueprint web.
The docker image should already have the shell dependencies loaded -- but this
is a note just in case you exit that generated shell with the dependencies.

Then build the webpage using `leanblueprint web`.

Then run `leanblueprint serve`.

Ensure you've run this docker image with port forwarding:
```
docker run -it --name cpp-lean-dev -e TERM=xterm-256color -p 8000:8000 cpp-lean:bundled
```

Then you can access the webpage from your local browser at
http://localhost:8000/
(even through the webpage is served from the docker container!).
