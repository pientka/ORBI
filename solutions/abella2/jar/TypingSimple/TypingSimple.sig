sig TypingSimple.

kind    tm, tp    type.

type    app       tm -> tm -> tm.
type    lam       tp -> (tm -> tm) -> tm.

type 	i	  tp.
type    arr     tp -> tp -> tp.

type    oft        tm -> tp -> o.
