From elpi Require Import elpi.
From mathcomp Require Import ssreflect ssrbool.

Require Import BinNums ZArith.

Require Import UrsusTVM.Solidity.tvmTypes.
Require Import UrsusTVM.Solidity.tvmFunc.
Require Import UrsusTVM.Solidity.tvmNotations.

Require Import UMLang.UrsusLib.
Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.

(* Require Import SuperLedger. *)
Require Import Generator.Util.

Local Open Scope N_scope.

(* Global Hint Unfold 
  (* upd_ledger_fields *)
  tvm_transfer_left 
  new_lvalueL
  wrapURValueL
  wrapURExpressionL
  wrapULExpressionL
  ursus_call_with_argsL
  wrapULExpression 
  rvalued_call_with_argsL
  URValueP0_RValuedWithArgsL
  UExpressionP0_LedgerableWithArgsL
  URValueP_Next_URValueDWithArgsL
  UExpressionP_Next_LedgerableWithRArgsL
  UExpressionP_Next_LedgerableWithLArgsL
  sInjectL
  ULtoRValueL
  tvm_transfer
  send_internal_message_
  send_internal_message
  send_internal_message_left
  send_internal_message_pre
  suicide_left
  suicide
      : unfolderDb. *)

Set Implicit Arguments.

Ltac generate_exec f :=
  let P  := fresh "P"  in
  let eq := fresh "eq" in
  let L  := fresh "L"  in
  intros;
  unfold f;
  autounfold with unfolderDb;
  fold XBool XUInteger XMaybe XList XProd XHMap;
  idtac "Start auto_build_P";
  repeat auto_build_P; idtac "auto_build_P is successful".

Ltac app tac name acc :=
  first [let arg := fresh "arg" in move=> arg ;
  let Y := constr:(acc arg) in 
  app tac name Y |
  idtac "app1 is successfull";
  idtac acc;
  let T := type of acc in idtac T;
  tac name acc;
  idtac "lets are done"].

Ltac app1 tac acc :=
  first [let arg := fresh "arg" in move=> arg ;
  let Y := constr:(acc arg) in 
  app1 tac Y |
  idtac "app1 is successfull";
  idtac acc;
  let T := type of acc in idtac T;
  tac acc;
  idtac "proof_of_2 is successfull"].

Ltac proof_of_2'' t :=
  let eP := eval hnf in t in
  lazymatch eP with
  | exist _ _ ?H => exact H
  end.

Ltac let_term_of_2' f := app let_term_of_2 f f.
Ltac flat_term_of_2' f := app flat_term_of_2 f f.
Ltac proof_of_2' f := app1 proof_of_2'' f.

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
  idtac "ledger destruction is successful";
  let f := fresh "f" in 
  let Heqf := fresh "Heqf" in
  remember exec as f eqn:Heqf; rewrite {1}Heqf;
  compute -[tvmTypes.xubint_booleq_obligation_1 N_eqb_opaque];
  compute -[N.eqb];
  idtac "exec computing is successful";
  repeat fold_bools;
  idtac "folding bools is successful";
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