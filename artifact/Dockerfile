FROM ubuntu:24.04

# Base dependencies
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      wget \
      git \
      sudo \
      libgmp-dev \
      opam \
      vim \
      pkg-config \
    && apt-get clean -y

# Create a new user and give them sudo rights
#ARG USER=user
#RUN useradd -d /home/$USER -s /bin/bash -m $USER
# NOTE: reuse the ubuntu user, instead of making a new one so we
# get UID=1000, which is the one most people have. This avoids file
# permission issues when using a devcontainer, unless we're unlucky.
# Such is life.
ARG USER=ubuntu
RUN echo "$USER ALL=NOPASSWD: ALL" >> /etc/sudoers
USER $USER
ENV HOME /home/$USER
WORKDIR $HOME

# Install OCaml
ARG OCAML_VERSION=4.14.0
RUN opam init --compiler=$OCAML_VERSION --disable-sandboxing
RUN opam option depext-run-installs=true
ENV OPAMYES=1

# Get F* master and build (install opam deps too)
RUN eval $(opam env) \
 && . $HOME/.profile \
 && git clone --depth=1 https://github.com/FStarLang/FStar \
 && cd FStar/ \
 && opam install --deps-only ./fstar.opam \
 && make -j$(nproc) ADMIT=1
RUN sudo ln -s $(realpath FStar/bin/fstar.exe) /usr/local/bin/fstar.exe

# Install z3 with F* script
RUN sudo ./FStar/.scripts/get_fstar_z3.sh /usr/local/bin

# Get karamel master and build (installing opam deps too, but ignoring fstar dependency)
RUN eval $(opam env) \
 && . $HOME/.profile \
 && git clone --depth=1 https://github.com/FStarLang/karamel \
 && cd karamel/ \
 && sed -i '/"fstar"/d' karamel.opam \
 && opam install --deps-only ./karamel.opam \
 && .docker/build/install-other-deps.sh \
 && make -j$(nproc)
RUN sudo ln -s $(realpath karamel/krml) /usr/local/bin/krml

ENV KRML_HOME /karamel/

WORKDIR $HOME

# Instrument .profile and .bashrc to set the opam switch. Note that this
# just appends the *call* to eval $(opam env) in these files, so we
# compute the new environments after the fact.
RUN echo 'eval $(opam env)' | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Also install OCaml 5.1.1 with domainslib (but do not make it the default)
RUN opam switch create 5.1.1
RUN opam install --switch=5.1.1 -- dune domainslib
RUN opam switch $OCAML_VERSION

# Copy and build pulse
COPY --chown=$USER pulsecore/ pulsecore/
RUN . $HOME/.bash_profile && cd pulsecore/ && make -j$(nproc)

RUN wget https://github.com/coder/code-server/releases/download/v4.98.0/code-server_4.98.0_amd64.deb \
 && sudo dpkg -i code-server*.deb \
 && rm code-server*.deb

RUN wget https://github.com/FStarLang/fstar-vscode-assistant/releases/download/v0.17.1/fstar-vscode-assistant-0.17.1.vsix \
 && code-server --install-extension fstar-vscode-assistant-*.vsix \
 && rm fstar-vscode-assistant-*.vsix

ENTRYPOINT code-server --auth none --bind-addr 0.0.0.0:8080 --disable-workspace-trust pulsecore
