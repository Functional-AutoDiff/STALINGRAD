/* gcc -o mplayerwin mplayerwin.c -lX11 */
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <X11/Xlib.h>

int main(int argc, char *argv[]) {
  Display *dpy = XOpenDisplay(NULL);
  Window p;
  int x, y, width, height;
  char command[1000];
  char hostname[256];
  if (argc!=7) {
    fprintf(stderr,
	    "usage: %s <parent> <x> <y> <width> <height> <pathname>\n",
	    argv[0]);
    exit(EXIT_FAILURE);
  }
  sscanf(argv[1], "%x", (unsigned int *)&p);
  sscanf(argv[2], "%d", &x);
  sscanf(argv[3], "%d", &y);
  sscanf(argv[4], "%d", &width);
  sscanf(argv[5], "%d", &height);
  if (gethostname(&hostname[0], 255)!=0) {
    fprintf(stderr, "Can't get hostname\n");
    exit(EXIT_FAILURE);
  }
  Window w = XCreateSimpleWindow(dpy, p, x, y, width, height, 0,
				 XWhitePixel(dpy, 0),
				 XWhitePixel(dpy, 0));
  XMapRaised(dpy, w);
  XFlush(dpy);
  /* needs work: to check overflow */
  /* -vo gl crashes tlamachilistli */
  /* -vo x11 doesn't crash tlamachilistli but doesn't resize */
  /* -vo xv doesn't display on external vga on thakaa */
  /* -vo xv doesn't resize in tightvnc */
  if (strcmp(hostname, "thakaa.ecn.purdue.edu")==0) {
    sprintf(&command[0],
	    "mplayer 2>/dev/null -really-quiet -wid 0x%x -vo gl %s",
	    (unsigned int)w,
	    argv[6]);
  }
  else if (strcmp(hostname, "etterretning.ecn.purdue.edu")==0||
           strcmp(hostname, "etterretning")==0) {
    sprintf(&command[0],
	    "mplayer 2>/dev/null -really-quiet -wid 0x%x -vo x11 -zoom %s",
	    (unsigned int)w,
	    argv[6]);
  }
  else {
    sprintf(&command[0],
	    "mplayer 2>/dev/null -really-quiet -wid 0x%x -vo xv %s",
	    (unsigned int)w,
	    argv[6]);
  }
  system(&command[0]);
  exit(EXIT_SUCCESS);
}
