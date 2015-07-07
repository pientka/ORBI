module TypingSimple.

oft (lam A M) (arr A B) :- pi x\ (oft x A => oft (M x) B).
oft (app M N) A :- oft M (arr B A), oft N B.
