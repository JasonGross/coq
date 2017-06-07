#!/usr/bin/env bash

#set -x
set -e

. ../template/init.sh

cd aggregate
coq_makefile -f _CoqProject -o Makefile
make pretty-timed TGTS="all" -j1 || exit $?

cd ../before
coq_makefile -f _CoqProject -o Makefile
make make-pretty-timed-before TGTS="all" -j1 || exit $?

cd ../after
coq_makefile -f _CoqProject -o Makefile
make make-pretty-timed-after TGTS="all" -j1 || exit $?
rm -f time-of-build-before.log
make print-pretty-timed-diff TIME_OF_BUILD_BEFORE_FILE=../before/time-of-build-before.log
cp ../before/time-of-build-before.log ./
make print-pretty-timed-diff || exit $?

for ext in "" .desired; do
    for file in time-of-build-before.log time-of-build-after.log time-of-build-both.log; do
	cat ${file}${ext} | sed s'/[0-9]//g' | sed s'/ *$//g' | sed s'/^-*$/------/g' | sed s'/  */ /g' | sed s'/\(Total.*\)-\(.*\)-/\1+\2+/g' > ${file}${ext}.processed
    done
done
for file in time-of-build-before.log time-of-build-after.log time-of-build-both.log; do
    diff -u $file.desired.processed $file.processed || exit $?
done

cd ../per-file-before
coq_makefile -f _CoqProject -o Makefile
make all TIMING=before -j2 || exit $?

cd ../per-file-after
coq_makefile -f _CoqProject -o Makefile
make all TIMING=after -j2 || exit $?

find ../per-file-before/ -name "*.before-timing" | xargs cp -t ./
make all.timing.diff -j2 || exit $?
cat A.v.timing.diff
echo

for ext in "" .desired; do
    for file in A.v.timing.diff; do
	cat ${file}${ext} | sed s'/[0-9]*\.[0-9]*//g' | sed s'/0//g' | sed s'/  */ /g' | sed s'/+/-/g' | sort > ${file}${ext}.processed
    done
done
for file in A.v.timing.diff; do
    diff -u $file.desired.processed $file.processed || exit $?
done

exit 0
