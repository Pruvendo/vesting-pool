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
  , coq.say {fun->prod LemmaTypeF}
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

  main [str Name] :- 
  get_eta Name Fun',
  coq.locate Name NameRef,
  coq.locate "upd_ledger_fields" UpdRef,
  coq.arguments.set-default-implicit NameRef,
  get_eta "upd_ledger_fields" 
  (fun _ _ l1\
   fun _ _ l2\
   fun _ _ l3\
   fun _ _ l4\
    (Upd' l1 l2 l3 l4)),
  pi l1 l2 l3 l4\ (Upd' l1 l2 l3 l4 = fun _ _ lC\ fun _ _ x\ Upd'' l1 l2 l3 l4 lC x),
  Upd = Upd'' _ _ _ _ _ _,
  pull_lambdas2' Upd Fun' (x\ y\ {{  StrictBinding lp:{{x}} lp:{{y}} }}) Fun'',
  std.assert-ok! (coq.typecheck Fun'' _) "type error while StrictBinding application",
  std.assert-ok! (coq.elaborate-skeleton Fun'' _ Fun) "can not infer parameters while StrictBinding application",
  get_fun "Uinterpreter" Uinterpreter,
  pull_lambdas Fun (c0 \ app
   [Uinterpreter, _, _, _, _, _, _, _, _, _, _, _,
                  _, _, _, _, _, _, _, _, _, _, _, _, c0]) UintNR',
  std.assert-ok! (coq.typecheck UintNR' _) "type error while Uinterpreter application",
  std.assert-ok! (coq.elaborate-skeleton UintNR' _ UintNR) "can not infer parameters while Uinterpreter application",

  % Generate exec state
  get_fun "exec_state" Exec_state,
  pull_lambdas UintNR
    (x\ fun `l` _ l\ app [Exec_state, _, _, _, _, _, x, l]) ES,
  std.assert-ok! (coq.typecheck ES _) "type error while exec_state application",
  std.assert-ok! (coq.elaborate-skeleton ES _ ESF) "can not infer parameters while exec_state application",
  std.assert-ok! (coq.typecheck ESF ESType) "type error while exec_state application",
  std.assert-ok! (coq.elaborate-skeleton ESType _ ESTypeF) "can not infer parameters while exec_state application",
  pull_lambdas ESF ( x\ {{ {t | t = lp:{{x}} } }}) LemmaType,
  std.assert-ok! (coq.elaborate-skeleton LemmaType _ LemmaTypeF) "can not infer parameters while lemma formulation",
  LemmaSigName is Name ^ "exec_sig",
  coq.env.add-const-ltac1 LemmaSigName {fun->prod LemmaTypeF} "generate_exec" [Name] _ _,
  get_def LemmaSigName LemmaSig _,
  proj1_sig LemmaSig Exec,
  proj2_sig LemmaSig ExecPrf,
  ExecName is Name ^ "exec",
  ExecLemmaName is Name ^ "E",
  coq.env.add-const ExecName Exec _ _ _,
  coq.say ExecName "is defined.",
  get_eta ExecName ExecTerm,
  get_fun "eq" Eq,
  arrow-head ESTypeF ESTypeFH,
  pull_lambdas2 ExecTerm ESF (x\ y\ app[Eq, ESTypeFH, x, y]) ExecTrem=ESF,
  coq.env.add-const ExecLemmaName ExecPrf {fun->prod ExecTrem=ESF} tt _,
  coq.say ExecLemmaName "is defined.",

  % Generate isErorr of eval state
  get_fun "eval_state" Eval_state,
  get_fun "isError" IsError,
  pull_lambdas UintNR
    (x\ fun `l` _ l\ app [IsError, _, _, app [Eval_state, _, _, _, _, _, x, l]]) EV,
  std.assert-ok! (coq.typecheck EV _) "type error while eval_state application",
  std.assert-ok! (coq.elaborate-skeleton EV _ EVF) "can not infer parameters while eval_state application",
  std.assert-ok! (coq.typecheck EVF EVType) "type error while eval_state application",
  std.assert-ok! (coq.elaborate-skeleton EVType _ EVTypeF) "can not infer parameters while eval_state application",
  pull_lambdas EVF ( x\ {{ {t | t = lp:{{x}} } }}) Lemma2Type,
  std.assert-ok! (coq.elaborate-skeleton Lemma2Type _ Lemma2TypeF) "can not infer parameters while lemma2 formulation",
  Lemma2SigName is "isError_" ^ Name ^ "sig",
  coq.env.add-const-ltac1 Lemma2SigName {fun->prod Lemma2TypeF} "generate_exec" [Name] _ _,
  get_def Lemma2SigName Lemma2Sig _,
  proj1_sig Lemma2Sig Eval,
  proj2_sig Lemma2Sig EvalPrf,
  EvalName is "isError_" ^ Name,
  EvalLemmaName is "isError_" ^ Name ^ "E",
  coq.env.add-const EvalName Eval _ _ _,
  coq.say EvalName "is defined.",
  get_eta EvalName EvalTerm,
  get_fun "eq" Eq,
  arrow-head EVTypeF EVTypeFH,
  pull_lambdas2 EvalTerm EVF (x\ y\ app[Eq, EVTypeFH, x, y]) EvalTrem=EVF,
  coq.env.add-const EvalLemmaName EvalPrf {fun->prod EvalTrem=EVF} tt _,
  coq.say EvalLemmaName "is defined.",

  %Compute generated execs
  % CLemmaName is Name ^ "'",
  % ComputedExecName is ExecName ^ "_computed",
  % ComputedExecLemmaName is ExecName ^ "E",
  % ComputedExecName' is ExecName ^ "_computed'",
  % pull_lambdas ExecTerm (x\ {{ P (lp:{{x}}) /\  P (lp:{{x}}) }}) FEC',
  % coq.elaborate-skeleton {fun->prod FEC'} _ FEC'' ok,
  % FEC = {{ False -> lp:{{FEC''}} }},
  % coq.env.add-const-ltac1 CLemmaName FEC "elpi_define_execs" [ExecName] tt _,
  % coq.say ComputedExecName "is defined.",
  % get_eta ComputedExecName ComputedExec,
  % get_def ComputedExecName' ComputedExec' T,
  % arrow-head T LT,
  % pull_lambdas2 ComputedExec' ComputedExec (x\y\ {{ @eq lp:{{LT}} lp:{{x}} lp:{{y}} }}) ComputedExecLemma',
  % fun->prod ComputedExecLemma' ComputedExecLemma,
  % coq.env.add-const-ltac1 ComputedExecLemmaName ComputedExecLemma "reflexivity_ltac" [] tt _,
  % coq.say ComputedExecLemmaName "is defined.",

  % CVLemmaName is Name ^ "''",
  % ComputedEvalName is EvalName ^ "_computed",
  % ComputedEvalLemmaName is EvalName ^ "E2",
  % ComputedEvalName' is EvalName ^ "_computed'",
  % pull_lambdas EvalTerm (x\ {{ P (lp:{{x}}) /\  P (lp:{{x}}) }}) FEVC',
  % coq.elaborate-skeleton {fun->prod FEVC'} _ FEVC'' ok,
  % FEVC = {{ False -> lp:{{FEVC''}} }},
  % coq.env.add-const-ltac1 CVLemmaName FEVC "elpi_define_execs" [EvalName] tt _,
  % coq.say ComputedEvalName "is defined.",
  % get_eta ComputedEvalName ComputedEval,
  % get_def ComputedEvalName' ComputedEval' TV,
  % arrow-head TV LTV,
  % pull_lambdas2 ComputedEval' ComputedEval (x\y\ {{ @eq lp:{{LTV}} lp:{{x}} lp:{{y}} }}) ComputedEvalLemma',
  % fun->prod ComputedEvalLemma' ComputedEvalLemma,
  % coq.env.add-const-ltac1 ComputedEvalLemmaName ComputedEvalLemma "reflexivity_ltac" [] tt _,
  % coq.say ComputedEvalLemmaName "is defined.",

  end.
}}.

Elpi Typecheck.

Elpi Export Generate_Super_Exec.


Elpi Command Foo.

Elpi Accumulate Db generator.db.

Elpi Accumulate lp:{{

  main [str Name] :-
  ExecName is Name ^ "exec",
  get_eta ExecName Exec,

  CLemmaName is Name ^ "'",
  ComputedExecName is ExecName ^ "_computed",
  ComputedExecLemmaName is ExecName ^ "E",
  ComputedExecName' is ExecName ^ "_computed'",
  pull_lambdas Exec (x\ {{ P (lp:{{x}}) /\  P (lp:{{x}}) }}) FEC',
  coq.elaborate-skeleton {fun->prod FEC'} _ FEC'' ok,
  FEC = {{ False -> lp:{{FEC''}} }},
  coq.say {coq.term->string FEC},
  coq.env.add-const-ltac1 CLemmaName FEC "elpi_define_execs" [ExecName] tt _,
  coq.say ComputedExecName "is defined.",
  get_eta ComputedExecName ComputedExec,
  get_def ComputedExecName' ComputedExec' T,
  arrow-head T LT,
  % coq.say {coq.term->string ComputedExec},
  % coq.say {coq.term->string ComputedExec'},
  pull_lambdas2 ComputedExec' ComputedExec (x\y\ {{ @eq lp:{{LT}} lp:{{x}} lp:{{y}} }}) ComputedExecLemma',
  fun->prod ComputedExecLemma' ComputedExecLemma,
  % coq.say {coq.term->string ComputedExecLemma},
  % coq.typecheck  ComputedExecLemma _ Res,
  % coq.say ComputedExecLemma,
  coq.env.add-const-ltac1 ComputedExecLemmaName ComputedExecLemma "reflexivity_ltac" [] tt _,
  coq.say ComputedExecLemmaName "is defined.",
  % coq.env.add-const "foo" ComputedExecLemma _ _ _,
  % coq.elaborate-skeleton {fun->prod ComputedExecLemma'} _  ComputedExecLemma ok,
  % coq.say {coq.term->string T},
  % coq.say {coq.term->string T'},
  % coq.say {coq.term->string ComputedExecLemma},
  % coq.say Res,
  end.
}}.

Elpi Typecheck.

