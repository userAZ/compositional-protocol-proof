# Compositional Protocol Proof

We prove that for a class of MSI and RCC-family protocols, this class of
protocols compose together when used for separate core-clusters (cluster 
protocols) connected by a (global) protocol of the family in the level above,
with translation shims to translate requests between cluster and global
protcols.

## Artifact Evaluation Instructions


Artifact for evaluation of "A Formally Verified Foundation for Compositional Heterogeneous Coherence"

decompress the .gz part of the .tar.gz file:
```
gunzip cpp-lean-bundled.tar.gz
```

Load in the docker image:
```
docker load < cpp-lean-bundled.tar
```

1) Start the container as root

```
docker start cpp-lean-flat
docker exec -u root -it cpp-lean-flat /bin/bash
```

2) Run unminimize
```
unminimize
```
(Answer y when prompted.)

3) Exit the root shell
```
exit
```
4) Start a nixuser shell
```
docker exec -u nixuser -it cpp-lean-flat /bin/bash
```
If the container isn’t running, you can instead do:
```
docker run -it --name cpp-lean-flat --user root -e TERM=xterm-256color -p 8000:8000 cpp-lean:flattened /bin/bash
```
then after unminimize, exit and re‑enter as nixuser with `docker exec -u nixuser`

The port forwarding is for looking at the generated webpage of `leanblueprint web` after running `leanblueprint serve`. It has a nice webpage with a graph of the theorem dependencies on other lemmas, theorems, and definitions.

Go into the directory "compositional-protocol-proof", that's where the artifact is located.

This repo also has a README.md and Instructions.pdf file. Follow the instructions in the README.md and Instructions.pdf file. The Instructions.pdf in the docker image is slightly stale.


Please check the pdf `Instructions.pdf`. It contains instructions
on running the artifact evaluation. This README.md mainly has some
extra insturctions for viewing the `leanblueprint web` website, if
you're interested in viewing it.

### Extra Help for Running `leanblueprint web` Website, and Loading It

If you want to run `leanblueprint web`, you may need to run the following command first:
```
chmod +rw blueprint/web/js/svgxuse.js blueprint/web/js/jquery.min.js blueprint/web/js/plastex.js blueprint/web/styles/* blueprint/web/symbol-defs.svg
```

Remember to run `nix-shell leanblueprint-shell.nix` to load the dependencies for leanblueprint web.
The docker image doesn't already have the shell dependencies loaded -- this
is a note as a reminder to start a generated shell with the dependencies.

Then build the webpage using `leanblueprint web`.

Then run `leanblueprint serve`.

Ensure you've run this docker image with port forwarding:
```
docker run -it --name cpp-lean-dev -e TERM=xterm-256color -p 8000:8000 cpp-lean:bundled
```

Then you can access the webpage from your local browser at
http://localhost:8000/
(even through the webpage is served from the docker container!).
