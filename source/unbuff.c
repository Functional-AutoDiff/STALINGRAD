// Run a command with it's standard output and stderr hooked to a
// pseudo-tty which we pass on to our stdout.  The point of all of
// this is so that the command's stdio will not buffer it's output.

// by Henry Cejtin
// modified by Barak Pearlmutter

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
  int		mfd, sfd, len;
  struct termios	tbuff;

  if (*++argv == NULL) {
    fprintf(stderr, "error: argument required\n");
    printf("Usage: unbuff command ...\n");
    printf("  Run a subsidiary command in such a way that its standard\n");
    printf("  output will not be buffered.\n");
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

    case 0:
      close(mfd);
      dup2(sfd, STDOUT_FILENO);
      dup2(sfd, STDERR_FILENO);
      close(sfd);
      tcgetattr(STDOUT_FILENO, &tbuff);
      tbuff.c_oflag &= ~ OPOST;
      tcsetattr(STDOUT_FILENO, TCSANOW, &tbuff);
      execvp(*argv, argv);
      // Note: these messages go via the parent, to stdout
      perror("error: execvp");
      fprintf(stderr, "Can't find %s\n", *argv);
      exit(1);

    default:
      close(sfd);
      {
	char buff[BUFSIZ];
	while (1) {
	  len = read(mfd, buff, BUFSIZ);
	  if (len <= 0)
	    break;
	  // Note: the following should really be in a loop, in case
	  // of partial success, due to Unix system call PC lusering
	  // and all that.
	  write(STDOUT_FILENO, buff, len);
	}
      }
    }
  return (0);
}

// make CFLAGS='-O2 -Wall' LOADLIBES=-lutil unbuff
