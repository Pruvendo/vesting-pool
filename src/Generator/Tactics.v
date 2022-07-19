From elpi Require Import elpi.
From mathcomp Require Import ssreflect ssrbool.

Require Import BinNums ZArith.

Require Import UMLang.UrsusLib.
Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.

(* Require Import SuperLedger. *)
Require Import Generator.Util.

Local Open Scope N_scope.

Global Hint Unfold 
  upd_ledger_fields
     : unfolderDb.

Set Implicit Arguments.

Ltac generate_exec f :=
  let P  := fresh "P"  in
  let eq := fresh "eq" in
  let L  := fresh "L"  in
  move=>*;
  eexists;
  match goal with |- _ = ?t => introduce t as P;
  [ unfold f;
    autounfold with unfolderDb;
    fold XBool XUInteger XMaybe XList XProd XHMap;
    repeat auto_build_P
  | extract_eq_flat of P as eq term L;  
    rewrite -eq ; clear eq
  ]
  end;
  cbv delta [L];
  exact/eq_refl.

Tactic Notation "fold_bools" := (match goal with 
| |- context C [match ?x with true => false | false => true end ]  =>
  change (match x with true => false | false => true end) with (~~ x)
| |- context  C [match ?x with true => ?y | false => false end ]  =>
  change (match x with true => y | false => false end) with (x && y)
| |- context  C [match ?x with true => true | false => ?y end ]  =>
  change (match x with true => true | false => y end ) with (orb x y)
end).

Tactic Notation "fold_bools" "in" ident(H) := (match goal with 
| H := context C [match ?x with true => false | false => true end ] |- _ =>
  change (match x with true => false | false => true end) with (~~ x) in H
| H := context  C [match ?x with true => ?y | false => false end ] |- _ =>
  change (match x with true => y | false => false end) with (x && y) in H
| H := context  C [match ?x with true => true | false => ?y end ] |- _ =>
  change (match x with true => true | false => y end ) with (orb x y) in H
end).

Ltac compute_exec
  LedgerLRecord
  MessagesAndEventsLRecord 
  LocalStateLRecord
  ContractLRecord
  VMStateLRecord
  exec := 
  let F := fresh "F" in
  move=> F;
  simpl;
  let l := fresh "l" in
  repeat (match goal with 
  | |- forall (_ : _), _ => 
    let x := fresh "x" in
    move=> x;  compute in x;
    match type of x with 
    | XUBInteger _  => revert x; case; intros ?
    | LedgerLRecord => revert x; move=> l
    | _ => revert x; intros ?
    end
  end);
  do 6? destruct l as [? l];
  repeat match goal with 
  | x : _ |- _ => 
    match type of x with 
    | MessagesAndEventsLRecord => 
      (have->: x = defMessagesAndEvents by destruct F); clear x
    | LocalStateLRecord => 
      (have->: x = defLocalState by destruct F); clear x
    end
  end;
  repeat
  match goal with 
  | c : _ |- _ => 
    match type of c with 
    | ContractLRecord =>
      repeat
      let x := fresh "x" in
      destruct c as [x c]; 
      compute in x;
      match type of x with 
      | XUBInteger _ => destruct x as [x]
      | _ => idtac
      end
    | VMStateLRecord => 
      repeat
      let x := fresh "x" in
      destruct c as [x c]; 
      compute in x;
      match type of x with 
      | XUBInteger _ => destruct x as [x]
      | _ => idtac
      end
    end
  end;
  let f := fresh "f" in 
  let Heqf := fresh "Heqf" in
  remember exec as f eqn:Heqf; rewrite {1}Heqf;
  compute -[tvmTypes.xubint_booleq_obligation_1];
  compute -[N.eqb];
  repeat fold_bools;
  rewrite Heqf; clear;
  repeat match goal with 
  | x : _ |- _ => revert x
  end.

Elpi Tactic define_execs.

Elpi Accumulate Db generator.db.

Elpi Accumulate lp:{{

  pred define_computed_exec i:term, o:term, o:term.
  define_computed_exec (prod I T x\ G x) (fun I T x\ A x) (fun I T x\ B x) :-
    !,
    pi x\ define_computed_exec (G x) (A x) (B x),
  end.
  define_computed_exec {{ P (lp:{{X}}) /\ P (lp:{{Y}}) }} X Y.

  solve (goal _ _ GoalType _ [trm T] as G) GL :- 
    coq.term->string T Name,
    define_computed_exec GoalType X Y,
    NameDef is Name ^ "_computed",
    NmaeDef' is NameDef ^ "'",
    coq.env.add-const-proofmode NameDef  X _ _ _,
    coq.env.add-const-proofmode NmaeDef' Y _ _ _,
    end.

}}.

Elpi Typecheck.

Ltac elpi_define_execs_pre 
  LedgerLRecord
  MessagesAndEventsLRecord 
  LocalStateLRecord
  ContractLRecord
  VMStateLRecord
  f := 
  compute_exec 
    LedgerLRecord
    MessagesAndEventsLRecord 
    LocalStateLRecord
    ContractLRecord
    VMStateLRecord 
    f;
  elpi define_execs ltac_term:(f);
  move=> *;
  exact (conj I I).

Ltac reflexivity_ltac := reflexivity.