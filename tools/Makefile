all: mplayerwin unbuff

CFLAGS=-O2 -g -Wall

mplayerwin: LOADLIBES=-lX11 -lxcb
unbuff: LOADLIBES=-lutil

clean:
	-rm -f mplayerwin unbuff mplayerwin.o unbuff.o

.PHONY: all clean
