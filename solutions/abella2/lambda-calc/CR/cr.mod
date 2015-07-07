%% Takahashi's proof of Church-Rosser using complete developments
%% Masako Takahashi, "Parallel reduction in lambda-calculus",
%%   Information and Computation 118(1), April 1995.
%%
%% Abella proof contributed by Randy Pollack

module cr.

% pure lambda terms
is_tm (app M N) :- is_tm M, is_tm N.
is_tm (abs R) :- pi x\ is_tm x => is_tm (R x).

% one step of Tait/Martin-Loef parallel reduction
pr1 (app T1 S1) (app T2 S2) :- pr1 T1 T2, pr1 S1 S2.
pr1 (abs S1) (abs S2) :- pi x\ pr1 x x => pr1 (S1 x) (S2 x).
pr1 (app (abs T1) S1) (T2 S2) :- pr1 (abs T1) (abs T2), pr1 S1 S2.

% a trm is not an abstraction
notabs (app M N).

% one step of complete development
cd1 (app T1 S1) (app T2 S2) :- notabs T1, cd1 T1 T2, cd1 S1 S2.
cd1 (abs S1) (abs S2) :- pi x\ notabs x => cd1 x x => cd1 (S1 x) (S2 x).
cd1 (app (abs T1) S1) (T2 S2) :- cd1 (abs T1) (abs T2), cd1 S1 S2.
