#!/usr/bin/fish


cmake -S. -Bbuild && make -C build && time ./bin/main
