sig EqualPoly.


kind    tm,tp             type.

type arr 		   tp -> tp -> tp.
type all 		    (tp -> tp) -> tp.

type    app            tm -> tm -> tm.
type    lam            (tm -> tm) -> tm.
type    tlam 	        (tp -> tm) -> tm.
type 	tapp 		 tm -> tp -> tm.

type    aeq    tm -> tm -> o.
type    atp    tp -> tp -> o.

type  is_tm	 tm -> o.
type  is_tp	 tp -> o.





