#! /bin/sh

set -e

autoreconf --install $*
libtoolize --install
