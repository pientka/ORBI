module Equal2.

aeq (app N M) (app P Q) :- aeq N P, aeq M Q.
aeq (abs R) (abs S) :- pi x\ aeq x x => aeq (R x) (S x).

aeq2 (app N M) (app P Q) :- aeq2 N P, aeq2 M Q.
aeq2 (abs R) (abs S) :- pi x\ pi y\ aeq2 x y => aeq2 (R x) (S y).
