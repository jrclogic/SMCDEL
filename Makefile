
default:
	@# Unfortunately hBDD does not install shared libs which
	@# are needed for the template haskell bits for smcdel-web
	LD_LIBRARY_PATH="/usr/local/lib/cudd/libso/" stack build

clean:
	stack clean
