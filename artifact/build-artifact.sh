#!/bin/bash

set -eux

NAME=pulsecore          # name of project, will show up in tarball
TAG=pulsecore-pldi2025  # name of docker tag and stem for filenames

# Create a clean checkout of pulse into pulse/
# Doing this instead of copying the root of the repo skips all git metadata

rm -rf $NAME
mkdir $NAME
git -C .. archive HEAD | tar -C $NAME -x

# Replace devcontainer definition
rm -rf $NAME/.devcontainer
cp -r devcontainer $NAME/.devcontainer
cp pulse.sh $NAME/pulse.sh

docker build -t $TAG .

docker save $TAG -o $TAG-docker.tar
gzip $TAG-docker.tar

tar czf $TAG-src.tar.gz $NAME/

echo 'Done!'
