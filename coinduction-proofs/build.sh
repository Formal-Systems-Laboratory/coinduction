#!/bin/sh
# This script is the main entry point for our shake-based build system.
# It compiles the Haskell program if needed, and calls it.
# The haskell program is passing extra arguments so
# it can use the shake databases in the root directory while still
# intepreting filenames relative to the directory build.sh was called from.
#
# Any arguments to build.sh are passed along as targets to build,
# The default target with no arguments is Files.mk.
#
# Targets can be .vo files and files named Files.mk.
#
# See the top of Build.hs for further documentation
#
# For the convenience of anyone working on the build system,
# Build.hs is recompiled if it has changed since the last time
# the executable was compiled. Even in this case, the shake
# database is NOT cleared (this is probably fine, but to
# recompile everything, delete .shake/.shake.database yourself).
set -e
TARGET_DIR=$PWD

hashok () {
  test -f .shake/hash.sha512 && shasum -a 512 --status -c .shake/hash.sha512;
}

rebuild () {
  mkdir -p .shake
  (cd .shake; cabal sandbox init; cabal install ../Build.cabal)
  ln -sf .cabal-sandbox/bin/Build .shake/build;
  shasum -a 512 Build.hs > .shake/hash.sha512;
}

cd $(dirname $0)
if ! hashok ; then rebuild; fi
.shake/build --relative-to "$TARGET_DIR" "$@";
