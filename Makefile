TJROOT = ~/.local/bin

.PHONY: all
all: main.lp

%.lpo : %.mod %.sig
	$(TJROOT)/tjcc $*

%.lp : %.lpo
	$(TJROOT)/tjlink $*

-include depend
depend: *.mod *.sig
	$(TJROOT)/tjdepend *.mod > depend-stage
	mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.lpo *.lp depend
