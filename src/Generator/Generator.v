From elpi Require Import elpi.

Require Import UMLang.SML_NG32.

Require Import Generator.Tactics Generator.Util.

Elpi Command Generate_Exec.

Elpi Accumulate Db generator.db.

Elpi Accumulate lp:{{


  main [str Name] :-
    get_eta Name Fun
  , coq.locate Name NameRef
  , coq.arguments.set-default-implicit NameRef
  , get_fun "Uinterpreter" Uinterpreter
  , pull_lambdas Fun (c0 \ app 
       [Uinterpreter, _, _, _, _, _, _, _, _, _, _, _,
                      _, _, _, _, _, _, _, _, _, _, _, _, c0]) UintNR'
  , std.assert-ok! (coq.typecheck UintNR' _) "type error while Uinterpreter application"
  , std.assert-ok! (coq.elaborate-skeleton UintNR' _ UintNR) "can not infer parameters while Uinterpreter application"
  , get_fun "exec_state" Exec_state
  , pull_lambdas UintNR 
     (x\ fun `l` _ l\ app [Exec_state, _, _, _, _, _, x, l]) ES
  , std.assert-ok! (coq.typecheck ES _) "type error while exec_state application"
  , std.assert-ok! (coq.elaborate-skeleton ES _ ESF) "can not infer parameters while exec_state application"
  , std.assert-ok! (coq.typecheck ESF ESType) "type error while exec_state application"
  , std.assert-ok! (coq.elaborate-skeleton ESType _ ESTypeF) "can not infer parameters while exec_state application"
  , pull_lambdas ESF ( x\ {{ {t | t = lp:{{x}} } }}) LemmaType
  , std.assert-ok! (coq.elaborate-skeleton LemmaType _ LemmaTypeF) "can not infer parameters while lemma formulation"
  , LemmaSigName is Name ^ "exec_sig"
  , coq.say {fun->prod LemmaTypeF} %DELETE
  , coq.say "Start proving" LemmaSigName "lemma"
  , coq.env.add-const-ltac1 LemmaSigName {fun->prod LemmaTypeF} "generate_exec" [Name] _ _
  , get_def LemmaSigName LemmaSig _
  , proj1_sig LemmaSig Exec
  , proj2_sig LemmaSig ExecPrf
  , ExecName is Name ^ "exec"
  , ExecLemmaName is Name ^ "E"
  , coq.env.add-const ExecName Exec _ _ _
  , get_eta ExecName ExecTerm
  , get_fun "eq" Eq
  , arrow-head ESTypeF ESTypeFH
  , pull_lambdas2 ExecTerm ESF (x\ y\ app[Eq, ESTypeFH, x, y]) ExecTrem=ESF
  , coq.env.add-const ExecLemmaName ExecPrf {fun->prod ExecTrem=ESF} tt _
  .
}}.

Elpi Typecheck.

Elpi Command Generate_Super_Exec.

Elpi Accumulate Db generator.db.

Elpi Accumulate lp:{{

  pred type_of_exec  i:string, i:term, o:term.
  type_of_exec Name (fun I T x\ ESF x) (prod I T x\ TOE x) :-
    pi x\ type_of_exec Name (ESF x) (TOE x),
  end.
  type_of_exec Name _ LedgerLRecord :-
    get_fun Name LedgerLRecord,
  end.

  pred run_generator i:string, i:string, i:string, i:term, o:term.
  run_generator Name TypeName ExecName ES ExecTerm :-
    std.assert-ok! (coq.typecheck ES _) "type error while exec_state application",
    std.assert-ok! (coq.elaborate-skeleton ES _ ESF) "can not infer parameters while exec_state application",
    std.assert-ok! (coq.typecheck ESF ESType) "type error while exec_state application",
    std.assert-ok! (coq.elaborate-skeleton ESType _ ESTypeF) "can not infer parameters while exec_state application",
    pull_lambdas ESF ( x\ {{ {t | t = lp:{{x}} } }}) LemmaType,
    type_of_exec TypeName ESF TOE,
    std.assert-ok! (coq.elaborate-skeleton LemmaType _ LemmaTypeF) "can not infer parameters while lemma formulation",
    LemmaSigName is ExecName ^ "_sig",
    coq.say "Start proving" LemmaSigName "lemma",
    % coq.env.add-const LemmaSigName {fun->prod LemmaTypeF} _ _ _,
    coq.env.add-const-ltac1 LemmaSigName {fun->prod LemmaTypeF} "generate_exec" [Name] _ _,
    coq.say LemmaSigName "is defined.",

    ExecName' is ExecName ^ "_trm",
    % coq.env.add-const ExecName' TOE _ _ _,
    coq.env.add-const-ltac1 ExecName' TOE "let_term_of_2'" [LemmaSigName] _ _,
    coq.say ExecName' "is defined.",

    % coq.env.add-const ExecName' TOE _ _ _,
    coq.env.add-const-ltac1 ExecName TOE "flat_term_of_2'" [ExecName'] _ _,
    coq.say ExecName "is defined.",

    get_eta ExecName ExecTerm,
    get_fun "eq" Eq,
    arrow-head ESTypeF ESTypeFH,
    pull_lambdas2 ExecTerm ESF (x\ y\ app[Eq, ESTypeFH, x, y]) ExecTrem=ESF,

    ExecLemmaName is ExecName ^ "E",
    %coq.env.add-const ExecLemmaName {fun->prod ExecTrem=ESF} _ _ _,
    coq.env.add-const-ltac1 ExecLemmaName {fun->prod ExecTrem=ESF} "proof_of_2'" [LemmaSigName] _ _,
    coq.say ExecLemmaName "is defined.",
  end.

  main [str Name] :- 
    get_eta Name Fun,
    coq.locate Name NameRef,
    % coq.locate "upd_ledger_fields" UpdRef,
    coq.arguments.set-default-implicit NameRef,
    % get_eta "upd_ledger_fields" 
    % (fun _ _ l1\
    % fun _ _ l2\
    % fun _ _ l3\
    % fun _ _ l4\
    %   (Upd' l1 l2 l3 l4)),
    % pi l1 l2 l3 l4\ (Upd' l1 l2 l3 l4 = fun _ _ lC\ fun _ _ x\ Upd'' l1 l2 l3 l4 lC x),
    % Upd = Upd'' _ _ _ _ _ _,
    % pull_lambdas2' Upd Fun' (x\ y\ {{  StrictBinding lp:{{x}} lp:{{y}} }}) Fun'',
    % std.assert-ok! (coq.typecheck Fun'' _) "type error while StrictBinding application",
    % std.assert-ok! (coq.elaborate-skeleton Fun'' _ Fun) "can not infer parameters while StrictBinding application",
    get_fun "Uinterpreter" Uinterpreter,
    pull_lambdas Fun (c0 \ app
    [Uinterpreter, _, _, _, _, _, _, _, _, _, _, _,
                    _, _, _, _, _, _, _, _, _, _, _, _, c0]) UintNR',
    std.assert-ok! (coq.typecheck UintNR' _) "type error while Uinterpreter application",
    std.assert-ok! (coq.elaborate-skeleton UintNR' _ UintNR) "can not infer parameters while Uinterpreter application",

    get_fun "exec_state" Exec_state,
    pull_lambdas UintNR
      (x\ fun `l` _ l\ app [Exec_state, _, _, _, _, _, x, l]) ES,

    get_fun "eval_state" Eval_state,
    get_fun "isError" IsError,
    pull_lambdas UintNR
      (x\ fun `l` _ l\ app [IsError, _, _, app [Eval_state, _, _, _, _, _, x, l]]) EV,

    %% Generate exec state
    ExecName is Name ^ "exec",
    EvalName is "isError_" ^ Name,
    run_generator Name "LedgerLRecord" ExecName ES _,
    run_generator Name "bool" EvalName EV _,
  end.
}}.

Elpi Typecheck.

Elpi Export Generate_Super_Exec.


Elpi Command Compute_Super_Exec.

Elpi Accumulate Db generator.db.

Elpi Accumulate lp:{{

  pred compute_generated i:string, i:string, i:string.
  compute_generated Name ExecName DummyName :- 
    get_eta ExecName ExecTerm,
    ComputedExecName is ExecName ^ "_computed",
    ComputedExecLemmaName is ExecName ^ "_computedE",
    ComputedExecName' is ExecName ^ "_computed'",
    pull_lambdas ExecTerm (x\ {{ P (lp:{{x}}) /\  P (lp:{{x}}) }}) FEC',
    coq.elaborate-skeleton {fun->prod FEC'} _ FEC'' ok,
    FEC = {{ False -> lp:{{FEC''}} }},
    coq.say "Start computing" ExecName,
    coq.env.add-const-ltac1 DummyName FEC "elpi_define_execs" [ExecName] tt _,
    coq.say ComputedExecName "is defined.",
    get_eta ComputedExecName ComputedExec,
    get_def ComputedExecName' ComputedExec' T,
    arrow-head T LT,
    pull_lambdas2 ComputedExec' ComputedExec (x\y\ {{ @eq lp:{{LT}} lp:{{x}} lp:{{y}} }}) ComputedExecLemma',
    fun->prod ComputedExecLemma' ComputedExecLemma,
    coq.env.add-const-ltac1 ComputedExecLemmaName ComputedExecLemma "reflexivity_ltac" [] tt _,
    coq.say ComputedExecLemmaName "is defined.",
  end.

  main [str Name] :-
    ExecName is Name ^ "exec",
    EvalName is "isError_" ^ Name,
    DummyName1 is Name ^ "'",
    DummyName2 is Name ^ "''",

    compute_generated Name ExecName DummyName1,
    compute_generated Name EvalName DummyName2,
  end.
}}.

Elpi Typecheck.

Elpi Export Compute_Super_Exec.
