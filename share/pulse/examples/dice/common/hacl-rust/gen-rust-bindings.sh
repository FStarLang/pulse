#!/usr/bin/env bash
set -e
set -x

# chdir to the current directory
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

# regenerate EverCrypt*.h
make -j -C ../hacl-c
! [[ -d c ]]
mkdir c
cp -v ../hacl-c/_output/*.h c/
cp -v ../hacl-c/*.h c/
for f in c/EverCrypt_*.h ; do echo '#include "'$(basename $f)'"' ; done > c/bindings.h

# generate EverCrypt*.rs in a Docker image
DOCKER_IMAGE_NAME=haclrustbindingsimg"$$"
echo $DOCKER_IMAGE_NAME
docker build -t $DOCKER_IMAGE_NAME -f rust.Dockerfile .

# copy everCrypt.rs from the Docker image
if  [[ -z "$PULSE_HOME" ]] ; then
    # assume share/pulse/examples/dice/common/hacl-rust
    PULSE_HOME=$(realpath $(pwd)/../../../../../..)
fi
DOCKER_CONTAINER_NAME=haclrustbindingscont"$$"
docker create --name $DOCKER_CONTAINER_NAME $DOCKER_IMAGE_NAME
docker cp $DOCKER_CONTAINER_NAME:/usr/src/hacl/evercrypt.rs $PULSE_HOME/pulse2rust/tests/src/dpe_/evercrypt.rs
docker rm $DOCKER_CONTAINER_NAME
