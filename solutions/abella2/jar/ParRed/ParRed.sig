sig ParRed.

kind    tm, tp                 type.

type    app                    tm -> tm -> tm.
type    lam                    (tm -> tm) -> tm.

type    arr                  tp -> tp -> tp.
type 	i		     tp.
type    oft                     tm -> tp -> o.
type    pr            tm -> tm -> o.

