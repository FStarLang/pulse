FROM ubuntu:24.04

SHELL ["/bin/bash", "-c"]

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
ARG USER=user
RUN useradd -d /home/$USER -s /bin/bash -m $USER
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
 && source $HOME/.profile \
 && git clone --depth=1 https://github.com/FStarLang/FStar \
 && cd FStar/ \
 && opam install --deps-only ./fstar.opam \
 && make -j$(nproc) ADMIT=1
RUN sudo ln -s $(realpath FStar/bin/fstar.exe) /usr/local/bin/fstar.exe

# Install z3 with F* script
RUN sudo ./FStar/.scripts/get_fstar_z3.sh /usr/local/bin

# Get karamel master and build (installing opam deps too, but ignoring fstar dependency)
RUN eval $(opam env) \
 && source $HOME/.profile \
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
RUN source .bash_profile && cd pulsecore/ && make -j$(nproc)
