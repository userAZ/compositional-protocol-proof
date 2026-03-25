FROM ubuntu:latest

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    git \
    build-essential \
    g++ \
    make \
    cmake \
    pkg-config \
    python3 \
    python3-dev \
    python3-venv \
    python3-pip \
    wget \
    gpg \
    xz-utils \
    unzip \
    graphviz \
    graphviz-dev \
    texlive-latex-extra \
    texlive-xetex \
    latexmk \
  && rm -rf /var/lib/apt/lists/*

# VS Code
RUN install -d /etc/apt/keyrings \
  && wget -qO- https://packages.microsoft.com/keys/microsoft.asc | gpg --dearmor > /etc/apt/keyrings/microsoft.gpg \
  && echo "deb [arch=amd64 signed-by=/etc/apt/keyrings/microsoft.gpg] https://packages.microsoft.com/repos/code stable main" > /etc/apt/sources.list.d/vscode.list \
  && apt-get update \
  && apt-get install -y --no-install-recommends code \
  && rm -rf /var/lib/apt/lists/*

# User for Nix/Lean work
RUN useradd --create-home --shell /bin/bash nixuser

# Lean (elan) + Lean4 toolchain (install as nixuser)
COPY lean-toolchain /tmp/lean-toolchain
RUN su - nixuser -c "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y"
ENV PATH=/home/nixuser/.elan/bin:$PATH
RUN su - nixuser -c "elan toolchain install \"$(cat /tmp/lean-toolchain)\" && elan default \"$(cat /tmp/lean-toolchain)\""

# Nix (single-user install as non-root, no profile modification)
RUN mkdir -m 0755 /nix \
  && chown -R nixuser:nixuser /nix
ENV NIX_INSTALLER_NO_MODIFY_PROFILE=1
RUN su - nixuser -c "curl -L https://nixos.org/nix/install | sh -s -- --no-daemon --yes"
ENV PATH=/home/nixuser/.nix-profile/bin:/home/nixuser/.nix-profile/sbin:$PATH

# CMurphi (Sapienza/RAISE copy) built via nix-shell
COPY murphi-shell.nix /opt/murphi-shell.nix
RUN su - nixuser -c "git clone --depth 1 https://bitbucket.org/mclab/cmurphi.git /home/nixuser/cmurphi" \
  && su - nixuser -c ". /home/nixuser/.nix-profile/etc/profile.d/nix.sh && nix-shell /opt/murphi-shell.nix --run \"make -C /home/nixuser/cmurphi/src\""
ENV PATH=/home/nixuser/cmurphi/src:$PATH

# leanblueprint via nix-shell (no project required)
COPY leanblueprint-shell.nix /opt/leanblueprint-shell.nix
RUN su - nixuser -c ". /home/nixuser/.nix-profile/etc/profile.d/nix.sh && nix-shell /opt/leanblueprint-shell.nix --run \"command -v leanblueprint\""

USER nixuser
WORKDIR /home/nixuser

CMD ["/bin/bash"]
