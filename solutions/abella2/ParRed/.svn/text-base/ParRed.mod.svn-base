module ParRed.

oft (lam R) (arr A B) :- pi x\ (oft x A => oft (R x) B).
oft (app M N) A :- oft M (arr B A), oft N B.

pr (app T1 S1) (app T2 S2) :- 
    pr T1 T2, 
    pr S1 S2.
pr (lam S1) (lam S2) :- 
    pi x\ pr x x => pr (S1 x) (S2 x).
% beta
pr (app (lam T1) S1) (T2 S2) :- 
    pi x\ pr x x => pr (T1 x) (T2 x), 
    pr S1 S2.

