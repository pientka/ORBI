sig reflG.

kind	nat	type.

kind    tm             type.


type 	z	nat.
type 	s 	nat -> nat.

type    app            tm -> tm -> tm.
type    lam            (tm -> tm) -> tm.

type    aeq,aeqxy    tm -> tm -> o.

type  is_tm	 tm -> o.

type  is_tm_n	 tm -> nat -> o.



