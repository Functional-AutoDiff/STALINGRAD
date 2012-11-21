all: mplayerwin unbuff sum

CFLAGS=-O2 -g -Wall

mplayerwin: LOADLIBES=-lX11 -lxcb
unbuff: LOADLIBES=-lutil

S2CC=s2cc

%: %.sc; $(S2CC) $(CFLAGS) -o $@ $<

clean:
	-rm -f mplayerwin unbuff mplayerwin.o unbuff.o
	-rm -f sum sum.o

.PHONY: all clean
