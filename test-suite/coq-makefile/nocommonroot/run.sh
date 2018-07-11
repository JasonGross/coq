#!/usr/bin/env bash

set -ex

. ../template/path-init.sh

coq_makefile a.v foo/b.v -R foo Foo -o Makefile || exit $?
make clean "$@" || exit $?
make "$@" || exit $?

coq_makefile a.v foo/b.v -Q foo Foo -o Makefile || exit $?
make clean "$@" || exit $?
make "$@" || exit $?

coq_makefile -f _CoqProject1 -o Makefile || exit $?
make clean "$@" || exit $?
make "$@" || exit $?

coq_makefile -f _CoqProject2 -o Makefile || exit $?
make clean "$@" || exit $?
make "$@" || exit $?

exit 0
