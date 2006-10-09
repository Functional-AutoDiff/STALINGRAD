// Run a command with its standard output and stderr hooked to a
// pseudo-tty which we pass on to our stdout.  The point of all of
// this is so that the command's stdio will not buffer its output.

// by Henry Cejtin
// modified and updated by Barak A. Pearlmutter

// CVS version control block - do not edit manually
//  $RCSfile$
//  $Revision$
//  $Date$
//  $Source$

#include <termios.h>
#include <stdarg.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <fcntl.h>
#include <pty.h>
#include <utmp.h>

int
main(int argc, char **argv)
{
  int		mfd, sfd, saved_stderr;
  struct termios	tbuff;

  if (*++argv == NULL) {
    fprintf(stderr, "error: argument required\n");
    printf("Usage: unbuff command ...\n");
    printf("  Run a subsidiary command in such a way that its standard\n");
    printf("  output will not be buffered, and that its standard error\n");
    printf("  will be merged with its standard output.\n");
    exit(1);
  }

  if (openpty(&mfd, &sfd, NULL, NULL, NULL) == -1) {
    perror("error: openpty");
    exit(1);
  }

  switch (fork())
    {

    case -1:
      perror("error: fork");
      exit(1);

    case 0:			// We are the child: exec

      // Errors that occur in the unbuff executable itself should go
      // to the parent stderr.  This is tricky because we may, by that
      // time, have already arranged for subprocess stderr to go to
      // stdout.  Therefore the parent stderr is saved away, and
      // restored if an error needs to be reported.

      saved_stderr = dup(STDERR_FILENO);
      if (saved_stderr == STDOUT_FILENO || saved_stderr == STDERR_FILENO)
	saved_stderr = -1;

      close(mfd);
      dup2(sfd, STDOUT_FILENO);
      dup2(sfd, STDERR_FILENO);
      close(sfd);
      tcgetattr(STDOUT_FILENO, &tbuff);
      tbuff.c_oflag &= ~ OPOST;
      tcsetattr(STDOUT_FILENO, TCSANOW, &tbuff);
      execvp(*argv, argv);

      // Errors via parent to stdout, unless parent stderr available.
      if (saved_stderr != -1) dup2(saved_stderr, STDERR_FILENO);
      perror("error: execvp");
      fprintf(stderr, "Can not find %s\n", *argv);
      exit(1);

    default:			// We are the parent: relay
      close(sfd);
      while (1) {
	char buff[BUFSIZ];
	int writ = 0;
	int len = read(mfd, buff, BUFSIZ);
	if (len <= 0)
	  break;
	// Loop, in case of partial writes.
	while (writ < len) {
	  int w = write(STDOUT_FILENO, buff+writ, len-writ);
	  if (w < 0) {
	    perror("error: write");
	    fprintf(stderr, "Output failed\n");
	    exit(1);
	  }
	  writ += w;
	}
      }
    }
  return (0);
}

// Local Variables:
// compile-command: "make CFLAGS='-O2 -Wall' LOADLIBES=-lutil unbuff"
// End:
