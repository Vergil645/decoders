#!/bin/bash

set -e


cmake -S. -Bbuild
make -C build

perf record -a -g -- ./bin/main
perf script > out.perf

/opt/flamegraph/stackcollapse-perf.pl out.perf > out.folded
/opt/flamegraph/flamegraph.pl "$@" out.folded > out.svg
