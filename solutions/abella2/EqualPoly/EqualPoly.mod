module EqualPoly.


% Reasoning about declarative and algorithmic equality 
is_tm (app E F) :- is_tm F, is_tm E.
is_tm (lam R) :- pi x\ is_tm x => is_tm (R x).
is_tm (tlam S) :- pi x\ is_tp x => is_tm (S x).
is_tm (tapp E T) :- is_tm E, is_tp T.

is_tp (arr T1 T2) :- is_tp T1, is_tp T2.
is_tp (all S) :- pi a\ is_tp a => is_tp (S a).

%% eq
aeq (app E F) (app P Q) :- aeq E P, aeq F Q.
aeq (tapp E1 T) (tapp E2 S)
        :- aeq E1 E2, atp T S.
aeq (lam R) (lam S) :- pi x\ aeq x x => aeq (R x) (S x).
aeq (tlam T) (tlam T1)
     :- (pi a\ atp a a => aeq (T a) (T1 a)).

atp (arr T1 T2) (arr S1 S2)
          :- atp T1 S1, atp T2 S2.
atp (all T) (all S)
      :- pi a\ atp a a => atp (T a) (S a). 

