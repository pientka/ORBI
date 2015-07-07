
.PHONY: all

 r : EqualUntyped.out
 ceq: ceq.out



# experiments
# xp: reflR-fg.out


# Everything after this point is generic and should be duplicated
# in user's makefiles

.PHONY: *.out
%.out :
	/home/alberto/systems/abella2.0/abella -i $*.thm

%.thc :
	/home/alberto/systems/abella2.0/abella $*.thm -c $*.thc

-include depend
depend: *.thm *.sig *.mod
	/home/alberto/systems/abella2.0/abella -M *.thm > depend-stage
	mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.thc depend
