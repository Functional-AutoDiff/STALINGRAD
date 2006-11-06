# Makefile for stalingrad

# Site configuration
# ------------------
INSTALLDIR  = $(QINSTALLDIR)
ARCHITECTURE_PATH = $(QARCHITECTURE_PATH)
INSTALLLIB  = $(INSTALLDIR)/lib
INSTALLLIBA = $(INSTALLLIB)/$(ARCHITECTURE_PATH)
INSTALLBIN  = $(INSTALLDIR)/bin
INSTALLBINA = $(INSTALLBIN)/$(ARCHITECTURE_PATH)

RELEASE_VERSION = 0.1
RELEASE_FILE = stalingrad-$(RELEASE_VERSION)

TARGETS = stalingrad

all: error$(ERROR_OK) $(TARGETS)

# To add a new architecture, add architecture specific lines.
# The line prefix should be '#`architecture-path` ', see examples below.
port:
	-rm -rf $(ARCHITECTURE_PATH)
	mkdir $(ARCHITECTURE_PATH)
	cd $(ARCHITECTURE_PATH); csh -cf "ln -s ../*.{sc,c,h} ."
	$(MAKE) port-makefile

port-makefile:
	echo "# This file was generated automatically.  Do not edit." >\
		$(ARCHITECTURE_PATH)/makefile
	echo "# ----------------------------------------------------" >>\
		$(ARCHITECTURE_PATH)/makefile
	echo ARCHITECTURE_PATH = $(ARCHITECTURE_PATH) >>\
		$(ARCHITECTURE_PATH)/makefile
	echo ERROR_OK = _no_error >> $(ARCHITECTURE_PATH)/makefile
	grep "^#$(ARCHITECTURE_PATH)" makefile | \
		sed "s/#$(ARCHITECTURE_PATH) //" >>\
			$(ARCHITECTURE_PATH)/makefile
	echo include ../makefile >> $(ARCHITECTURE_PATH)/makefile

error:
	@echo "Do 'make port' to create an architecture specific directory."
	@exit 1

error_no_error:

# Architecture specific variables
# -------------------------------
#sun4-SunOS-4.1.3 CC = gcc
#sun4-SunOS-4.1.3 CFLAGS = -O2
#sun4-SunOS-4.1.3 SCCFLAGS = -O2
#sun4-SunOS-4.1.3 SCCLDFLAGS =
#sun4-SunOS-4.1.3 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#sun4-SunOS-4.1.3       stalingradlib-*.o -L/usr/openwin/lib -lX11 -lm

#sun4m-SunOS-5.4 CC = gcc
#sun4m-SunOS-5.4 CFLAGS = -O2
#sun4m-SunOS-5.4 SCCFLAGS = -O2
#sun4m-SunOS-5.4 SCCLDFLAGS =
#sun4m-SunOS-5.4 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#sun4m-SunOS-5.4       stalingradlib-*.o\
#sun4m-SunOS-5.4       -L/usr/openwin/lib -R/usr/openwin/lib -lX11\
#sun4m-SunOS-5.4       -L/usr/ucblib -R/usr/ucblib -lucb -lm

#sun4m-SunOS-5.5 CC = gcc
#sun4m-SunOS-5.5 CFLAGS = -O2
#sun4m-SunOS-5.5 SCCFLAGS = -O2
#sun4m-SunOS-5.5 SCCLDFLAGS =
#sun4m-SunOS-5.5 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#sun4m-SunOS-5.5       stalingradlib-*.o\
#sun4m-SunOS-5.5       -L/usr/openwin/lib -R/usr/openwin/lib -lX11\
#sun4m-SunOS-5.5       -L/usr/ucblib -R/usr/ucblib -lucb -lm

#sun4u-SunOS-5.6 CC = gcc
#sun4u-SunOS-5.6 CFLAGS = -O2
#sun4u-SunOS-5.6 SCCFLAGS = -O2
#sun4u-SunOS-5.6 SCCLDFLAGS =
#sun4u-SunOS-5.6 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#sun4u-SunOS-5.6       stalingradlib-*.o\
#sun4u-SunOS-5.6       -L/usr/openwin/lib -R/usr/openwin/lib -lX11\
#sun4u-SunOS-5.6       -L/usr/ucblib -R/usr/ucblib -lucb -lm

#sun4u-SunOS-5.8 CC = gcc
#sun4u-SunOS-5.8 CFLAGS = -O2
#sun4u-SunOS-5.8 SCCFLAGS = -O2
#sun4u-SunOS-5.8 SCCLDFLAGS =
#sun4u-SunOS-5.8 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#sun4u-SunOS-5.8       stalingradlib-*.o\
#sun4u-SunOS-5.8       -L/usr/openwin/lib -R/usr/openwin/lib -lX11\
#sun4u-SunOS-5.8       -L/usr/ucblib -R/usr/ucblib -lucb -lm

#i586-Linux-2.0.0 CC = gcc
#i586-Linux-2.0.0 CFLAGS = -O2 -DLINUX
#i586-Linux-2.0.0 SCCFLAGS = -O2
#i586-Linux-2.0.0 SCCLDFLAGS =
#i586-Linux-2.0.0 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i586-Linux-2.0.0       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i586-Linux-2.0.34 CC = egcs
#i586-Linux-2.0.34 CFLAGS = -O2 -DLINUX
#i586-Linux-2.0.34 SCCFLAGS = -O2
#i586-Linux-2.0.34 SCCLDFLAGS =
#i586-Linux-2.0.34 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i586-Linux-2.0.34       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i586-Linux-2.0.35 CC = egcs
#i586-Linux-2.0.35 CFLAGS = -O2 -DLINUX
#i586-Linux-2.0.35 SCCFLAGS = -O2
#i586-Linux-2.0.35 SCCLDFLAGS =
#i586-Linux-2.0.35 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i586-Linux-2.0.35       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.0.18 CC = gcc
#i686-Linux-2.0.18 CFLAGS = -O2 -DLINUX
#i686-Linux-2.0.18 SCCFLAGS = -O2
#i686-Linux-2.0.18 SCCLDFLAGS =
#i686-Linux-2.0.18 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.0.18       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.0.27 CC = gcc
#i686-Linux-2.0.27 CFLAGS = -O2 -DLINUX
#i686-Linux-2.0.27 SCCFLAGS = -O2
#i686-Linux-2.0.27 SCCLDFLAGS =
#i686-Linux-2.0.27 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.0.27       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.0.30 CC = gcc
#i686-Linux-2.0.30 CFLAGS = -O2 -DLINUX
#i686-Linux-2.0.30 SCCFLAGS = -O2
#i686-Linux-2.0.30 SCCLDFLAGS =
#i686-Linux-2.0.30 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.0.30       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.0.32 CC = gcc
#i686-Linux-2.0.32 CFLAGS = -O2 -DLINUX
#i686-Linux-2.0.32 SCCFLAGS = -O2
#i686-Linux-2.0.32 SCCLDFLAGS =
#i686-Linux-2.0.32 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.0.32       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.0.33 CC = gcc
#i686-Linux-2.0.33 CFLAGS = -O2 -DLINUX
#i686-Linux-2.0.33 SCCFLAGS = -O2
#i686-Linux-2.0.33 SCCLDFLAGS =
#i686-Linux-2.0.33 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.0.33       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.0.34 CC = egcs
#i686-Linux-2.0.34 CFLAGS = -O2 -DLINUX
#i686-Linux-2.0.34 SCCFLAGS = -O2
#i686-Linux-2.0.34 SCCLDFLAGS =
#i686-Linux-2.0.34 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.0.34       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.0.35 CC = egcs
#i686-Linux-2.0.35 CFLAGS = -O2 -DLINUX
#i686-Linux-2.0.35 SCCFLAGS = -O2
#i686-Linux-2.0.35 SCCLDFLAGS =
#i686-Linux-2.0.35 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.0.35       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.2.1 CC = egcs
#i686-Linux-2.2.1 CFLAGS = -O2 -DLINUX
#i686-Linux-2.2.1 SCCFLAGS = -O2
#i686-Linux-2.2.1 SCCLDFLAGS =
#i686-Linux-2.2.1 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.2.1       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.2.5 CC = egcs
#i686-Linux-2.2.5 CFLAGS = -O2 -DLINUX
#i686-Linux-2.2.5 SCCFLAGS = -O2
#i686-Linux-2.2.5 SCCLDFLAGS =
#i686-Linux-2.2.5 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.2.5       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#i686-Linux-2.2.5-15 CC = egcs
#i686-Linux-2.2.5-15 CFLAGS = -O2 -DLINUX
#i686-Linux-2.2.5-15 SCCFLAGS = -O2
#i686-Linux-2.2.5-15 SCCLDFLAGS =
#i686-Linux-2.2.5-15 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.2.5-15       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.2.10 CC = egcs
#i686-Linux-2.2.10 CFLAGS = -O2 -DLINUX
#i686-Linux-2.2.10 SCCFLAGS = -O2
#i686-Linux-2.2.10 SCCLDFLAGS =
#i686-Linux-2.2.10 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.2.10       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.2.12-20 CC = egcs
#i686-Linux-2.2.12-20 CFLAGS = -O2 -DLINUX
#i686-Linux-2.2.12-20 SCCFLAGS = -O2
#i686-Linux-2.2.12-20 SCCLDFLAGS =
#i686-Linux-2.2.12-20 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.2.12-20       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.2.12-20       stalingradlib-*.o\
#i686-Linux-2.2.12-20       -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.2.12-20smp CC = egcs
#i686-Linux-2.2.12-20smp CFLAGS = -O2 -DLINUX
#i686-Linux-2.2.12-20smp SCCFLAGS = -O2
#i686-Linux-2.2.12-20smp SCCLDFLAGS =
#i686-Linux-2.2.12-20smp LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.2.12-20smp       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.2.12-20smp       stalingradlib-*.o\
#i686-Linux-2.2.12-20smp       -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.3.42 CC = egcs
#i686-Linux-2.3.42 CFLAGS = -O2 -DLINUX
#i686-Linux-2.3.42 SCCFLAGS = -O2
#i686-Linux-2.3.42 SCCLDFLAGS =
#i686-Linux-2.3.42 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.3.42       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.3.42       stalingradlib-*.o\
#i686-Linux-2.3.42       -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.2-2 CC = gcc
#i686-Linux-2.4.2-2 CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.2-2 SCCFLAGS = -O2
#i686-Linux-2.4.2-2 SCCLDFLAGS =
#i686-Linux-2.4.2-2 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.2-2       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.2-2       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.2-2smp CC = gcc
#i686-Linux-2.4.2-2smp CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.2-2smp SCCFLAGS = -O2
#i686-Linux-2.4.2-2smp SCCLDFLAGS =
#i686-Linux-2.4.2-2smp LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.2-2smp       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.2-2smp       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.7 CC = gcc
#i686-Linux-2.4.7 CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.7 SCCFLAGS = -O2
#i686-Linux-2.4.7 SCCLDFLAGS =
#i686-Linux-2.4.7 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.7       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.7       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.7-10 CC = gcc
#i686-Linux-2.4.7-10 CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.7-10 SCCFLAGS = -O2
#i686-Linux-2.4.7-10 SCCLDFLAGS =
#i686-Linux-2.4.7-10 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.7-10       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.7-10       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.7-10smp CC = gcc
#i686-Linux-2.4.7-10smp CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.7-10smp SCCFLAGS = -O2
#i686-Linux-2.4.7-10smp SCCLDFLAGS =
#i686-Linux-2.4.7-10smp LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.7-10smp       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.7-10smp       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.9-13 CC = gcc
#i686-Linux-2.4.9-13 CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.9-13 SCCFLAGS = -O2
#i686-Linux-2.4.9-13 SCCLDFLAGS =
#i686-Linux-2.4.9-13 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.9-13       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.9-13       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.17-0.13ecn1 CC = gcc
#i686-Linux-2.4.17-0.13ecn1 CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.17-0.13ecn1 SCCFLAGS = -O2
#i686-Linux-2.4.17-0.13ecn1 SCCLDFLAGS =
#i686-Linux-2.4.17-0.13ecn1 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.17-0.13ecn1       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.17-0.13ecn1       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.18-4_72smp CC = gcc
#i686-Linux-2.4.18-4_72smp CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.18-4_72smp SCCFLAGS =
#i686-Linux-2.4.18-4_72smp SCCLDFLAGS =
#i686-Linux-2.4.18-4_72smp LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.18-4_72smp       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.18-4_72smp       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.18-19.7.x CC = gcc
#i686-Linux-2.4.18-19.7.x CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.18-19.7.x SCCFLAGS = -O2
#i686-Linux-2.4.18-19.7.x SCCLDFLAGS =
#i686-Linux-2.4.18-19.7.x LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.18-19.7.x       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.18-19.7.x       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.4.18-24.7.x CC = gcc
#i686-Linux-2.4.18-24.7.x CFLAGS = -O2 -DLINUX
#i686-Linux-2.4.18-24.7.x SCCFLAGS = -O2
#i686-Linux-2.4.18-24.7.x SCCLDFLAGS =
#i686-Linux-2.4.18-24.7.x LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.4.18-24.7.x       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.4.18-24.7.x       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.6.8.1 CC = gcc
#i686-Linux-2.6.8.1 CFLAGS = -O2 -DLINUX
#i686-Linux-2.6.8.1 SCCFLAGS =
#i686-Linux-2.6.8.1 SCCLDFLAGS =
#i686-Linux-2.6.8.1 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.6.8.1       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.6.8.1       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.6.8-1-686 CC = gcc
#i686-Linux-2.6.8-1-686 CFLAGS = -O2 -DLINUX
#i686-Linux-2.6.8-1-686 SCCFLAGS =
#i686-Linux-2.6.8-1-686 SCCLDFLAGS =
#i686-Linux-2.6.8-1-686 LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.6.8-1-686       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.6.8-1-686       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

#i686-Linux-2.6.15-1-k7-smp CC = gcc
#i686-Linux-2.6.15-1-k7-smp CFLAGS = -O2 -DLINUX
#i686-Linux-2.6.15-1-k7-smp SCCFLAGS =
#i686-Linux-2.6.15-1-k7-smp SCCLDFLAGS =
#i686-Linux-2.6.15-1-k7-smp LRL = $(INSTALLLIBA)/QobiScheme.a\
#i686-Linux-2.6.15-1-k7-smp       $(INSTALLLIBA)/scxl.a\
#i686-Linux-2.6.15-1-k7-smp       stalingradlib-*.o -L/usr/X11R6/lib -lX11 -lm

# missing i386-FreeBSD-2.2-STABLE

#alpha-OSF1-V3.2 CC = cc
#alpha-OSF1-V3.2 CFLAGS = -O4 -migrate -ieee_with_no_inexact
#alpha-OSF1-V3.2 SCCFLAGS = -migrate -ieee_with_no_inexact
#alpha-OSF1-V3.2 SCCLDFLAGS = -migrate
#alpha-OSF1-V3.2 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#alpha-OSF1-V3.2       stalingradlib-*.o -lX11 -lm

#alpha-OSF1-V4.0 CC = cc
#alpha-OSF1-V4.0 CFLAGS = -O4 -migrate -ieee_with_no_inexact
#alpha-OSF1-V4.0 SCCFLAGS = -migrate -ieee_with_no_inexact
#alpha-OSF1-V4.0 SCCLDFLAGS = -migrate
#alpha-OSF1-V4.0 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#alpha-OSF1-V4.0       stalingradlib-*.o -lX11 -lm

#alpha-Linux-2.0.35 CC = egcs
#alpha-Linux-2.0.35 CFLAGS = -O2 -DLINUX
#alpha-Linux-2.0.35 SCCFLAGS = -O2
#alpha-Linux-2.0.35 SCCLDFLAGS =
#alpha-Linux-2.0.35 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#alpha-Linux-2.0.35       stalingradlib-*.o -L/usr/X11/lib -lX11 -lm

#IP7-IRIX-4.0.5 CC = gcc
#IP7-IRIX-4.0.5 CFLAGS = -O2
#IP7-IRIX-4.0.5 SCCFLAGS = -O2
#IP7-IRIX-4.0.5 SCCLDFLAGS =
#IP7-IRIX-4.0.5 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#IP7-IRIX-4.0.5       stalingradlib-*.o -lX11 -lm

#IP12-IRIX-4.0.5 CC = gcc
#IP12-IRIX-4.0.5 CFLAGS = -O2
#IP12-IRIX-4.0.5 SCCFLAGS = -O2
#IP12-IRIX-4.0.5 SCCLDFLAGS =
#IP12-IRIX-4.0.5 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#IP12-IRIX-4.0.5       stalingradlib-*.o -lX11 -lm

#IP22-IRIX-5.3 CC = cc
#IP22-IRIX-5.3 CFLAGS = -O2 -non_shared
#IP22-IRIX-5.3 SCCFLAGS = -O2 -non_shared
#IP22-IRIX-5.3 SCCLDFLAGS = -non_shared
#IP22-IRIX-5.3 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#IP22-IRIX-5.3       $(INSTALLLIBA)/libX11.a stalingradlib-*.o -lm

#IP25-IRIX64-6.2 CC = cc
#IP25-IRIX64-6.2 CFLAGS = -O2 -non_shared
#IP25-IRIX64-6.2 SCCFLAGS = -O2 -non_shared
#IP25-IRIX64-6.2 SCCLDFLAGS = -non_shared
#IP25-IRIX64-6.2 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#IP25-IRIX64-6.2       $(INSTALLLIBA)/libX11.a stalingradlib-*.o -lm

#IP28-IRIX64-6.2 CC = cc
#IP28-IRIX64-6.2 CFLAGS = -O2 -non_shared
#IP28-IRIX64-6.2 SCCFLAGS = -O2 -non_shared
#IP28-IRIX64-6.2 SCCLDFLAGS = -non_shared
#IP28-IRIX64-6.2 LRL = $(INSTALLLIBA)/QobiScheme.a $(INSTALLLIBA)/scxl.a\
#IP28-IRIX64-6.2       $(INSTALLLIBA)/libX11.a stalingradlib-*.o -lm

arc:
	../arc stalingrad

clean:
	-rm -f *.o core a.out

real-clean: clean
	-rm -f $(TARGETS)

install: all
	cp $(TARGETS) $(INSTALLBINA)/.

uninstall:
	cd $(INSTALLBINA); rm -rf $(TARGETS)

release:
	-rm -rf $(RELEASE_FILE) $(RELEASE_FILE).tar*
	mkdir $(RELEASE_FILE)
	cp makefile *.{sc,c,h} $(RELEASE_FILE)/.
	tar cvf $(RELEASE_FILE).tar ./$(RELEASE_FILE)
	compress $(RELEASE_FILE).tar
	-rm -rf $(RELEASE_FILE)
	mv $(RELEASE_FILE).tar.Z ../releases/.

publish: release
	cd ..; publish stalingrad $(RELEASE_VERSION)

# Compilation rules and dependencies
# ----------------------------------
stalingradlib = stalingradlib-stuff.o\
		stalingradlib-double-c.o

stalingradlib-stuff.sch: stalingradlib-*.sc
	sch stalingradlib-stuff stalingradlib-*.sc

stalingradlib-stuff.o: stalingradlib-stuff.sch c-externals.sc\
stalingradlib-stuff.sc
	scc -cc $(CC) $(SCCFLAGS) -c stalingradlib-stuff.sc
	-rm -f stalingradlib-stuff.c

stalingradlib-double-c.o: stalingradlib-double-c.c
	$(CC) $(CFLAGS) -o stalingradlib-double-c.o\
             -c stalingradlib-double-c.c

stalingrad.sch: stalingrad.sc stalingradlib-*.sc
	sch -main stalingrad stalingradlib-*.sc

stalingrad.o: stalingrad.sch stalingrad.sc
	scc -cc $(CC) $(SCCFLAGS) -c stalingrad.sc
	-rm -f stalingrad.c

stalingrad: stalingrad.o $(stalingradlib)
	scc -cc $(CC) $(SCCLDFLAGS) -o stalingrad\
            stalingrad.o $(LRL)
