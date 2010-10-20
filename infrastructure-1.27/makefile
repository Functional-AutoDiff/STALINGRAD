RELEASE_VERSION = 1.27
RELEASE_FILE = infrastructure-$(RELEASE_VERSION)

release:
	-rm -rf $(RELEASE_FILE) $(RELEASE_FILE).tar*
	mkdir $(RELEASE_FILE)
	cp README $(RELEASE_FILE)/.
	cp architecture-path $(RELEASE_FILE)/.
	cp archive-date $(RELEASE_FILE)/.
	cp build $(RELEASE_FILE)/.
	cp scc $(RELEASE_FILE)/.
	cp scc-egcs $(RELEASE_FILE)/.
	cp 15mar93.tar $(RELEASE_FILE)/.
	cp LINUX-15mar93.patches $(RELEASE_FILE)/.
	cp FREEBSD-15mar93.patches $(RELEASE_FILE)/.
	cp SOL2-15mar93.patches $(RELEASE_FILE)/.
	cp apply.h $(RELEASE_FILE)/.
	cp apply.c $(RELEASE_FILE)/.
	cp objects.h $(RELEASE_FILE)/.
	cp objects.c $(RELEASE_FILE)/.
	cp heap-linux.h $(RELEASE_FILE)/.
	cp cio-linux.c $(RELEASE_FILE)/.
	cp cio-sparc.c $(RELEASE_FILE)/.
	cp heap-linux.c $(RELEASE_FILE)/.
	cp scinit-linux.c $(RELEASE_FILE)/.
	cp linux.s $(RELEASE_FILE)/.
	cp alpha-linux.S $(RELEASE_FILE)/.
	cp scrt4-linux.sc $(RELEASE_FILE)/.
	cp scrt4-freebsd.sc $(RELEASE_FILE)/.
	cp scrt4-sparc.sc $(RELEASE_FILE)/.
	cp scrt4-sgimips.sc $(RELEASE_FILE)/.
	cp scrt4-aosf.sc $(RELEASE_FILE)/.
	cp makefile $(RELEASE_FILE)/.
	cp makefile-sunos5-scrt $(RELEASE_FILE)/.
	cp makefile-irix5-cdecl $(RELEASE_FILE)/.
	cp makefile-irix5-scrt $(RELEASE_FILE)/.
	cp makefile-irix5-scsc $(RELEASE_FILE)/.
	cp makefile-irix5-test $(RELEASE_FILE)/.
	cp makefile-irix5-xlib $(RELEASE_FILE)/.
	cp makefile-alpha-linux-cdecl $(RELEASE_FILE)/.
	cp makefile-alpha-linux-scrt $(RELEASE_FILE)/.
	cp makefile-alpha-linux-scsc $(RELEASE_FILE)/.
	cp makefile-alpha-linux-server $(RELEASE_FILE)/.
	cp makefile-alpha-linux-test $(RELEASE_FILE)/.
	cp makefile-alpha-linux-xlib $(RELEASE_FILE)/.
	cp makefile-aosf-cdecl $(RELEASE_FILE)/.
	cp makefile-aosf-scrt $(RELEASE_FILE)/.
	cp makefile-aosf-scsc $(RELEASE_FILE)/.
	cp makefile-aosf-test $(RELEASE_FILE)/.
	cp makefile-aosf-xlib $(RELEASE_FILE)/.
	cp makefile-linux-cdecl $(RELEASE_FILE)/.
	cp makefile-linux-scrt $(RELEASE_FILE)/.
	cp makefile-linux-scsc $(RELEASE_FILE)/.
	cp makefile-linux-server $(RELEASE_FILE)/.
	cp makefile-linux-test $(RELEASE_FILE)/.
	cp makefile-linux-xlib $(RELEASE_FILE)/.
	cp makefile-linux-egcs-cdecl $(RELEASE_FILE)/.
	cp makefile-linux-egcs-scrt $(RELEASE_FILE)/.
	cp makefile-linux-egcs-scsc $(RELEASE_FILE)/.
	cp makefile-linux-egcs-server $(RELEASE_FILE)/.
	cp makefile-linux-egcs-test $(RELEASE_FILE)/.
	cp makefile-linux-egcs-xlib $(RELEASE_FILE)/.
	cp libX11.a $(RELEASE_FILE)/.
	cp crt1.o $(RELEASE_FILE)/.
	cp crtn.o $(RELEASE_FILE)/.
	cp libc.a $(RELEASE_FILE)/.
	cp libm.a $(RELEASE_FILE)/.
	cp xwss.sc $(RELEASE_FILE)/.
	tar cvf $(RELEASE_FILE).tar ./$(RELEASE_FILE)
	compress $(RELEASE_FILE).tar
	-rm -rf $(RELEASE_FILE)
	mv $(RELEASE_FILE).tar.Z releases/.

publish: release
	publish infrastructure $(RELEASE_VERSION)
