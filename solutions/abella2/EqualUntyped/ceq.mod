module ceq.

accumulate EqualUntyped.

deq (app E F) (app P Q) :- deq E P, deq F Q.
deq (lam M) (lam N) :-  pi x\   is_tm x => deq x x => deq (M x) (N x).
deq M M :- is_tm M. 
deq M N :-  deq M M', deq M' N.
deq M N :- deq N M.
