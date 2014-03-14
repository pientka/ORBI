module reflG.


% Reasoning about declarative and algorithmic equality 
is_tm (app E F)  :- is_tm F, is_tm E.
is_tm (lam R)  :- pi x\ is_tm x  => is_tm (R x).


aeq (app E F) (app P Q) :- aeq E P, aeq F Q.
aeq (lam R) (lam S) :- pi x\  is_tm x => aeq x x =>  aeq (R x) (S x).

