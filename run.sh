AFL_NO_FORKSRV=1 ~/Programs/afl-2.10b/afl-fuzz -d -Q -f false.vo -i inputs -o outputs ./bin/coqchk -o -boot -norec false
AFL_NO_FORKSRV=1 ~/Programs/afl-2.10b/afl-fuzz -d -Q -f false.vo -i inputs -o outputs ./bin/votour false.vo
