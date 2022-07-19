From elpi Require Import elpi.

Elpi Db generator.db lp:{{

  pred end.
  end :- 1 = 1.

  pred fun->prod i:term, o:term.
  fun->prod (fun I T x\ X x) (prod I T x\ Y x) :- 
    !,
    pi x\ fun->prod (X x) (Y x),
  end.
  fun->prod X X.

  pred get_eta i:string, o:term.
  get_eta Name T :-
    get_def Name F _,
    get_fun Name FN,
    list_args F FN [] T,
  end.

  pred list_args i:term, i:term, i:list term, o:term.
  list_args (fun I T x\ X x) N Ans (fun I T x\ Z x) :- 
    !,
    pi x\ list_args (X x) N [x|Ans] (Z x),
  end.
  list_args Y N Ans (app [N| Ans']) :- 
    std.rev Ans Ans',
  end.

  pred eta i:term, i:term, o:term.
  eta (fun I T x\ X x) N (fun I T y\ Y y) :- 
    !,
    pi x\ eta (X x) N (Y x),
  end.
  eta X N Y :- Y = N.

  pred pull_lambdas i:term, i:term -> term, o:term.

  pull_lambdas (fun I T x\ X x) F (fun I T x\ Ans x) :- 
    pi x\ pull_lambdas (X x) F (Ans x).
  pull_lambdas T F Ans :- Ans = F T.

  pred pull_lambdas2 i:term, i:term, i:term -> term -> term, o:term.
  pull_lambdas2 (fun I T x\ X x) (fun I T x\ Y x) F (fun I T x\ Ans x) :- 
    pi x\ pull_lambdas2 (X x) (Y x) F (Ans x).
  pull_lambdas2 T1 T2 F Ans :- Ans = F T1 T2.

  pred pull_lambdas2' i:term, i:term, i:term -> term -> term, o:term.

  pull_lambdas2' X (fun I T x\ Y x) F (fun I T x\ Ans x) :- 
    pi x \ pull_lambdas2' X (Y x) F (Ans x).
  pull_lambdas2' (fun I T x\ X x) Y F (fun I T x\ Ans x) :- 
    pi x \ pull_lambdas2' (X x) Y F (Ans x).
  pull_lambdas2' T1 T2 F Ans :- Ans = F T1 T2.

  pred get_def i:string, o:term, o:Type.

  get_def Name Body Type :-
    coq.locate Name (const C),
    coq.env.const C (some Body) Type,
  end.

  pred get_fun i:string, o:term.
  get_fun Name Body :-
    coq.locate Name C,
   Body = global C,
  end.

  pred proj1_sig i:term, o:term.
  proj1_sig (fun I T x\ X x) (fun I T y\ Y y) :- 
    !,
    pi x\ proj1_sig (X x) (Y x),
  end.
  proj1_sig (app [_, _, _ , Y, _]) Y.

  pred proj2_sig i:term, o:term.
  proj2_sig (fun I T x\ X x) (fun I T y\ Y y) :- 
    !,
    pi x\ proj2_sig (X x) (Y x),
  end.
  proj2_sig (app [_, _, _ , _, Y]) Y.

  pred arrow-head i:term, o:term.
  arrow-head (prod _ _ x\ X) Y :- arrow-head X Y.
  arrow-head Y Y.

}}.

Definition P {T : Type} (t : T) := True.

Opaque P.