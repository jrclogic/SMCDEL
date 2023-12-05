FROM mcr.microsoft.com/devcontainers/base:jammy

USER vscode
WORKDIR /home/vscode

# Install dependencies
RUN sudo apt-get update && sudo apt-get install -y build-essential curl libffi-dev libffi7 libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5 texlive-latex-extra graphviz dot2tex

ENV PATH="/home/${USERNAME}/.local/bin:/home/${USERNAME}/.cabal/bin:/home/${USERNAME}/.ghcup/bin:$PATH"

RUN echo "export PATH=${PATH}" >> /home/${USERNAME}/.profile

# ghcup is a replacement for the haskell platform. It manages the development env easily. 
# We use the official instalation script
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_MINIMAL=1 BOOTSTRAP_HASKELL_NONINTERACTIVE=1 sh

# Set up the environment. This will install the default versions of every tool.
RUN /home/vscode/.ghcup/bin/ghcup install ghc 9.4.7
RUN /home/vscode/.ghcup/bin/ghcup install hls
RUN /home/vscode/.ghcup/bin/ghcup install stack
RUN /home/vscode/.ghcup/bin/ghcup install cabal

# change stack's configuration to use system installed ghc.
# By default, stack tool will download its own version of the compiler,
# Setting up this configuration will avoid downloading haskell compiler twice.
RUN /home/vscode/.ghcup/bin/stack config set install-ghc --global false
RUN /home/vscode/.ghcup/bin/stack config set system-ghc --global true
