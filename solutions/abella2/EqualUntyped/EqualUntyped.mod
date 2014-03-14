module EqualUntyped.


% Reasoning about declarative and algorithmic equality 
is_tm (app M N)  :- is_tm N, is_tm M.
is_tm (lam M)  :- pi x\ is_tm x  => is_tm (M x).

aeq (app M1 M2) (app N1 N2) :- aeq M1 N1, aeq M2 N2.
aeq (lam M) (lam N) :- pi x\ aeq x x => aeq (M x) (N x).

