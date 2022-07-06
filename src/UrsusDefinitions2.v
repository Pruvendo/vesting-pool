Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Setoid. 
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Ascii.

Require Import FinProof.Common.
Require Import FinProof.MonadTransformers21.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib. 
Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Require Import UrsusStdLib.Solidity.stdTypes.
Require Import UrsusStdLib.Solidity.stdErrors.
Require Import UrsusStdLib.Solidity.stdFunc.
Require Import UrsusStdLib.Solidity.stdNotations.
Require Import UrsusStdLib.Solidity.stdUFunc.
Require Import UrsusStdLib.Solidity.stdFuncNotations.

Require Import UrsusTVM.Solidity.tvmTypes.
Require Import UrsusTVM.Solidity.tvmFunc.
Require Import UrsusTVM.Solidity.tvmNotations.
Require Import UrsusTVM.Solidity.tvmCells.

Require Import UrsusDefinitions.

Import UrsusNotations.
Local Open Scope xlist_scope.
Local Open Scope record.
Local Open Scope program_scope.
Local Open Scope glist_scope.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.

From elpi Require Import elpi.

(* Require Import interfaces.IGiver.
Require Import interfaces.ICrash. *)

Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.


(* Ltac unfoldTerm T := fun a b x =>
( let TT := fresh "TT" in
  let HTT := fresh "HeqTT" in
  remember (T a b x) as TT;  
  unfold doCrash in HTT; 
  exact TT). *)

Elpi Tactic add_context.

Elpi Accumulate Db global_fields_utils.

Elpi Accumulate lp:{{
solve _ _  :- 
  get_name "LocalStateLRecord" LSLR,
  coq.env.add-context-proofmode (some "Foo") {{
      LocalStateField XHMap lp:LSLR boolean
    }} tt tt.
}}.

Elpi Typecheck.



Elpi Tactic clear_file.

Elpi Accumulate lp:{{

solve (goal _Ctx _ _GoalType _ [trm FN]) _ :- 
  coq.term->string FN FNS,
  (K  is size FNS),
  (FNSS is substring FNS 1 (K - 2)),
  open_out FNSS OS,
  flush OS, 
  close_out OS.

}}.

Elpi Typecheck.

Elpi Db bk_translate_utils lp:{{

pred is_hole i:term.
is_hole T :- get_name "S" SS, /* put here any absurd */
  ((T = app [SS | _]) ; ((T = let _ _ T1 x \ x), (T1 = app [SS | _]))).

pred translate_urscalar i:term, i:goal-ctx, i:int, o:int, o:string.
translate_urscalar (app L) Ctx HoleId HoleId SS :- 
  coq.say "urscalar" ,
  std.rev L [V|_],
  /* coq.say V, */
  (get_name "default" Def, (V = app [Def|_]), (SS is "$Default$"); coq.term->string V SS).


pred translate_ultorvalue i:term, i:goal-ctx, i:int, o:int, o:string.
translate_ultorvalue (app L) Ctx HoleId NewHoleId SS :- 
coq.say "ultorvalue" ,
  std.rev L [LV|_],
  translate_lvalue LV Ctx HoleId NewHoleId SS.

pred translate_wrapurvalue i:term, i:goal-ctx, i:int, o:int, o:string.
translate_wrapurvalue (app L) Ctx HoleId NewHoleId SS :- 
coq.say "wrapurvalue" ,
  std.rev L [RV|_],
  translate_rfunc RV Ctx HoleId NewHoleId SS.

pred translate_rfunc i:term, i:goal-ctx, i:int, o:int, o:string.
translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "uneg" UNeg,
  (L = [UNeg|_]),
  coq.say "rfunc uneg" ,
  std.rev L [Arg|_],
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is "!" ^ ArgS.

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uplus" UPlus,
  (L = [UPlus|_]),
  coq.say "rfunc uplus" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is "(" ^ ArgS1 ^ " + " ^ ArgS2 ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uminus" UMinus,
  (L = [UMinus|_]),
  coq.say "rfunc uminus" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " - " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "umult" UMult,
  (L = [UMult|_]),
  coq.say "rfunc umult",
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " * " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "udiv" UDiv,
  (L = [UDiv|_]),
  coq.say "rfunc udiv" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " / " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "ultb" ULtb,
  (L = [ULtb|_]),
  coq.say "rfunc ultb" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " < " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uleb" ULeb,
  (L = [ULeb|_]),
  coq.say "rfunc uleb" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " <= " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "ugtb" UGtb,
  (L = [UGtb|_]),
  coq.say "rfunc ugtb" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " > " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "ugeb" UGeb,
  (L = [UGeb|_]),
  coq.say "rfunc ugeb" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " >= " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "umod" UMod,
  (L = [UMod|_]),
  coq.say "rfunc umod" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " % " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uxor" UXor,
  (L = [UXor|_]),
  coq.say "rfunc uxor" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " ^ " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uright" URight,
  (L = [URight|_]),
  coq.say "rfunc uright" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " >> " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uleft" ULeft,
  (L = [ULeft|_]),
  coq.say "rfunc uleft" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " << " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uand" UAnd,
  (L = [UAnd|_]),
  coq.say "rfunc uand" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " & " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uor" UOr,
  (L = [UOr|_]),
  coq.say "rfunc uor" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " | " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "umin" UMin,
  (L = [UMin|_]),
  coq.say "rfunc umin" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is "math.min(" ^ ArgS1 ^ "," ^ ArgS2 ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "umax" UMax,
  (L = [UMax|_]),
  coq.say "rfunc umax" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is "math.max(" ^ ArgS1 ^ "," ^ ArgS2 ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "ueqb" UEqb,
  (L = [UEqb|_]),
  coq.say "rfunc ueqb" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " == " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uneqb" UNeqb,
  (L = [UNeqb|_]),
  coq.say "rfunc uneqb" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " != " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uband" UBand,
  (L = [UBand|_]),
  coq.say "rfunc uband" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " && " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "ubor" UBor,
  (L = [UBor|_]),
  coq.say "rfunc ubor" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ " || " ^ ArgS2 .

translate_rfunc (app L) Ctx HoleId NewHoleId3 SS :- 
  get_name "umuldiv" UMuldiv,
  (L = [UMuldiv|_]),
  coq.say "rfunc umuldiv" ,
  std.rev L [ Arg3 | [ Arg2 | [ Arg1 | _ ] ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  translate_rvalue Arg3 Ctx NewHoleId2 NewHoleId3 ArgS3,
  SS is "math.muldiv(" ^ ArgS1 ^ ", " ^ ArgS2 ^ ", " ^ ArgS3 ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "ubitsize" UuBitsize,
  (L = [UuBitsize|_]),
  coq.say "rfunc ubitsize" ,
  std.rev L [ Arg | _ ] ,

  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
coq.say "777" ArgS "777",
  SS is "bitSize(" ^ ArgS ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "uubitsize" UuBitsize,
  (L = [UuBitsize|_]),
  coq.say "rfunc uubitsize" ,
  std.rev L [ Arg | _ ] ,

  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
coq.say "777" ArgS "777",
  SS is "uBitSize(" ^ ArgS ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uhmap_find_with_default" Uhmap_find_with_default,
  (L = [Uhmap_find_with_default|_]),
  coq.say "rfunc uhmap_find_with_default" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ "[ " ^ ArgS2 ^ " ]".

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uhmap_fetch" Uuhmap_fetch,
  (L = [Uuhmap_fetch|_]),
  coq.say "rfunc uhmap_fetch" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".fetch( " ^ ArgS2 ^ " )".

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uhmap_exists" Uuhmap_exists,
  (L = [Uuhmap_exists|_]),
  coq.say "rfunc uhmap_exists" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".exists( " ^ ArgS2 ^ " )".

translate_rfunc (app L) Ctx HoleId NewHoleId3 SS :- 
  get_name "uhmap_insert" Uuhmap_insert,
  (L = [Uuhmap_insert|_]),
  coq.say "rfunc uhmap_insert" ,
  std.rev L [ Arg3 | [ Arg2 | [ Arg1 | _ ] ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  translate_rvalue Arg3 Ctx NewHoleId2 NewHoleId3 ArgS3,
  SS is ArgS1 ^ ".insert(" ^ ArgS2 ^ ", " ^ ArgS3 ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uhmap_delete" Uuhmap_delete,
  (L = [Uuhmap_delete|_]),
  coq.say "rfunc uhmap_delete" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".delete(" ^ ArgS2 ^ ")" .



translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "uhmap_min" Uuhmap_min,
  (L = [Uuhmap_min|_]),
  coq.say "rfunc uhmap_min" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".min()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "uhmap_max" Uuhmap_max,
  (L = [Uuhmap_max|_]),
  coq.say "rfunc uhmap_max" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".max()" .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uhmap_next" Uuhmap_next,
  (L = [Uuhmap_next|_]),
  coq.say "rfunc uhmap_next" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".next(" ^ ArgS2 ^ ")" .


translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uhmap_prev" Uuhmap_prev,
  (L = [Uuhmap_prev|_]),
  coq.say "rfunc uhmap_prev" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".prev(" ^ ArgS2 ^ ")" .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uhmap_next_or_eq" Uuhmap_next_or_eq,
  (L = [Uuhmap_next_or_eq|_]),
  coq.say "rfunc uhmap_next_or_eq" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".nextOrEq(" ^ ArgS2 ^ ")" .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "uhmap_prev_or_eq" Uuhmap_prev_or_eq,
  (L = [Uuhmap_prev_or_eq|_]),
  coq.say "rfunc uhmap_prev_or_eq" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".prevOrEq(" ^ ArgS2 ^ ")" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "umaybe_has_value" Uumaybe_has_value,
  (L = [Uumaybe_has_value|_]),
  coq.say "rfunc umaybe_has_value" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".hasValue()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "umaybe_set" Uumaybe_set,
  (L = [Uumaybe_set|_]),
  coq.say "rfunc umaybe_set" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".set()" .

translate_rfunc (app L) Ctx HoleId NewHoleId3 SS :- 
  get_name "xstring_substr" Uxstring_substr,
  (L = [Uxstring_substr|_]),
  coq.say "rfunc xstring_substr" ,
  std.rev L [ Arg3 | [ Arg2 | [ Arg1 | _ ] ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  translate_rvalue Arg3 Ctx NewHoleId2 NewHoleId3 ArgS3,
  SS is ArgS1 ^ ".substr(" ^ ArgS2 ^ ", " ^ ArgS3 ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "xstring_find" Uxstring_find,
  (L = [Uxstring_find|_]),
  coq.say "rfunc xstring_find" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".find(" ^ ArgS2 ^ ")" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "length" Ulength,
  (L = [Ulength|_]),
  coq.say "rfunc length" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".length()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "xqueue_pop" Uxqueue_pop,
  (L = [Uxqueue_pop|_]),
  coq.say "rfunc xqueue_pop" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".pop()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "xqueue_push" Uxqueue_push,
  (L = [Uxqueue_push|_]),
  coq.say "rfunc xqueue_push" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".push()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "xqueue_none" Uxqueue_none,
  (L = [Uxqueue_none|_]),
  coq.say "rfunc xqueue_none" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".end()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "xqueue_front" Uxqueue_front,
  (L = [Uxqueue_front|_]),
  coq.say "rfunc xqueue_front" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".front()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "xqueue_back" Uxqueue_back,
  (L = [Uxqueue_back|_]),
  coq.say "rfunc xqueue_back" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".back()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "is_empty_" Uis_empty_,
  (L = [Uis_empty_|_]),
  coq.say "rfunc is_empty_" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".empty()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "msg_sender" Utvm_msg_sender,
  (L = [Utvm_msg_sender|_]),
  coq.say "rfunc msg_sender" ,
NewHoleId is HoleId,
  SS is "msg.sender" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "msg_pubkey" Utvm_msg_pubkey,
  (L = [Utvm_msg_pubkey|_]),
  coq.say "rfunc msg_pubkey" ,
NewHoleId is HoleId,
  SS is "msg.pubkey" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "msg_value" Utvm_msg_value,
  (L = [Utvm_msg_value|_]),
  coq.say "rfunc msg_value" ,
NewHoleId is HoleId,
  SS is "msg.value" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "now" Utvm_now,
  (L = [Utvm_now|_]),
  coq.say "rfunc now" ,
NewHoleId is HoleId,
  SS is "now" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "address" Utvm_address,
  (L = [Utvm_address|_]),
  coq.say "rfunc address" ,
NewHoleId is HoleId,
  SS is "address(this)" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "_isStdZero" Uaddress_isStdZero,
  (L = [Uaddress_isStdZero|_]),
  coq.say "rfunc _isStdZero" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".isStdZero()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "address_this__balance" Utvm_balance,
  (L = [Utvm_balance|_]),
  coq.say "rfunc address_this__balance" ,
NewHoleId is HoleId,
  SS is "address(this).balance" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "tvm_code" Utvm_code,
  (L = [Utvm_code|_]),
  coq.say "rfunc tvm_code" ,
NewHoleId is HoleId,
  SS is "tvm.code()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "tvm_currectCode" Utvm_currectCode,
  (L = [Utvm_currectCode|_]),
  coq.say "rfunc tvm_currectCode" ,
NewHoleId is HoleId,
  SS is "tvm.currectCode()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "msg_data" Utvm_msg_data,
  (L = [Utvm_msg_data|_]),
  coq.say "rfunc msg_data" ,
NewHoleId is HoleId,
  SS is "msg.data" .

 translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "address_this_" Uaddress_this_,
  (L = [Uaddress_this_|_]),
  coq.say "rfunc address_this_" ,
NewHoleId is HoleId,
  SS is "address(this)" .

/* translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "tvm_rawReserve_left" Utvm_rawReserve_left,
  (L = [Utvm_rawReserve_left|_]),
  coq.say "rfunc tvm_rawReserve_left" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is "tvm.rawReserve(" ^ ArgS1 ^ "," ^ ArgS2 ^ ")" . */

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "tvm_pubkey" Utvm_pubkey,
  (L = [Utvm_pubkey|_]),
  coq.say "rfunc tvm_pubkey" ,
NewHoleId is HoleId,
  SS is "tvm.pubkey()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "tvm_hash" Utvm_hash,
  (L = [Utvm_hash|_]),
  coq.say "rfunc tvm_hash" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is "tvm.hash(" ^ ArgS ^ ")" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "tvm_buildDataInit" Utvm_buildDataInit,
  (L = [Utvm_buildDataInit|_]),
  coq.say "rfunc tvm_buildDataInit" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is "tvm.buildDataInit(" ^ ArgS ^ ")" .

translate_rfunc (app L) Ctx HoleId NewHoleId4 SS :- 
  get_name "tvm_stateInitHash" Utvm_stateInitHash,
  (L = [Utvm_stateInitHash|_]),
  coq.say "rfunc tvm_stateInitHash" ,
  std.rev L [ Arg4 | [ Arg3 | [ Arg2 | [ Arg1 | _ ] ] ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  translate_rvalue Arg3 Ctx NewHoleId2 NewHoleId3 ArgS3,
  translate_rvalue Arg4 Ctx NewHoleId3 NewHoleId4 ArgS4,
  SS is "tvm.stateInitHash(" ^ ArgS1 ^ ", " ^ ArgS2 ^ ", " ^ ArgS3 ^ ", " ^ ArgS4 ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId3 SS :- 
  get_name "tvm_buildStateInit" Utvm_buildStateInit,
  (L = [Utvm_buildStateInit|_]),
  coq.say "rfunc tvm_buildStateInit" ,
  std.rev L  [ Arg3 | [ Arg2 | [ Arg1 | _ ] ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  translate_rvalue Arg3 Ctx NewHoleId2 NewHoleId3 ArgS3,
  SS is "tvm.buildStateInit(" ^ ArgS1 ^ ", " ^ ArgS2 ^ ", " ^ ArgS3 ^ ")".

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "_toCell" Ubuilder_to_cell,
  (L = [Ubuilder_to_cell|_]),
  coq.say "rfunc _toCell" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".toCell()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "_toSlice" Ucell_to_slice,
  (L = [Ucell_to_slice|_]),
  coq.say "rfunc _toSlice" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".toSlice()" .

translate_rfunc (app L) Ctx HoleId NewHoleId SS :- 
  get_name "_refs" Uslice_refs,
  (L = [Uslice_refs|_]),
  coq.say "rfunc _refs" ,
  std.rev L [ Arg | _ ] ,
  translate_rvalue Arg Ctx HoleId NewHoleId ArgS,
  SS is ArgS ^ ".refs()" .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "storeRef" UstoreRef,
  (L = [UstoreRef|_]),
  coq.say "rfunc storeRef" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".storeRef(" ^ ArgS2 ^ ")" .

translate_rfunc (app L) Ctx HoleId NewHoleId2 SS :- 
  get_name "builder_store" Ubuilder_store,
  (L = [Ubuilder_store|_]),
  coq.say "rfunc builder_store" ,
  std.rev L [ Arg2 | [ Arg1 | _ ] ],
  translate_rvalue Arg1 Ctx HoleId     NewHoleId1 ArgS1,
  translate_rvalue Arg2 Ctx NewHoleId1 NewHoleId2 ArgS2,
  SS is ArgS1 ^ ".store(" ^ ArgS2 ^ ")" .

/* такой функции она не находит: builder_stslice */
/* translate_rfunc (app L) Ctx HoleId NewHoleId1 SS :- 
  get_name "builder_stslice" Ubuilder_stslice,
  (L = [Ubuilder_stslice|_]),
  coq.say "rfunc builder_stslice" ,
  std.rev L [ Arg1 | _ ] ,
  translate_rvalue Arg1 Ctx HoleId NewHoleId1 ArgS1,
  SS is ArgS1 ^ ".toSlice()" . */

translate_rfunc (app L) Ctx HoleId NewHoleId1 SS :- 
  get_name "_depth" Ubuilder_depth,
  (L = [Ubuilder_depth|_]),
  coq.say "rfunc _depth" ,
  std.rev L [ Arg1 | _ ] ,
  translate_rvalue Arg1 Ctx HoleId NewHoleId1 ArgS1,
  SS is ArgS1 ^ ".depth()" .

/* translate_rfunc (app L) Ctx HoleId NewHoleId1 SS :- 
  get_name "cell_depth" Ucell_depth,
  (L = [Ucell_depth|_]),
  coq.say "rfunc cell_depth" ,
  std.rev L [ Arg1 | _ ] ,
  translate_rvalue Arg1 Ctx HoleId NewHoleId1 ArgS1,
  SS is ArgS1 ^ ".depth()" .

translate_rfunc (app L) Ctx HoleId NewHoleId1 SS :- 
  get_name "slice_depth" Uslice_depth,
  (L = [Uslice_depth|_]),
  coq.say "rfunc slice_depth" ,
  std.rev L [ Arg1 | _ ] ,
  translate_rvalue Arg1 Ctx HoleId NewHoleId1 ArgS1,
  SS is ArgS1 ^ ".depth()" . */

translate_rfunc (app L) Ctx HoleId NewHoleId1 SS :- 
  get_name "suicide_left" Usuicide_left,
  (L = [Usuicide_left|_]),
  coq.say "rfunc suicide_left" ,
  std.rev L [ Arg1 | _ ] ,
  translate_rvalue Arg1 Ctx HoleId NewHoleId1 ArgS1,
  SS is "selfdestruct(" ^ ArgS1 ^ ")" .

translate_rfunc _ _  HoleId HoleId "NOT_IMPLEMENTED". 

pred find_ctx_var i:term, i:list prop, o:string.
find_ctx_var  X [decl X S _ | _ ] SS :- coq.name->id S SS. /* fun `a` Ty x \ F x*/
find_ctx_var  X [_ | PS] S :- find_ctx_var X PS S.
/* find_ctx_var _ [] _ :- coq.error "error"  , false */

/* make one function for the next three */
pred find_level i:list prop, o:term.
find_level [def _ N _ (app [HL, L]) | _] L :- 
  coq.name->id N "HLevel", 
  get_name "HoleLevel" HL, !,
  coq.say "yay lvl".
find_level [_P|PS] L :- /* coq.say P, */ find_level PS L.
find_level [] _ :-  coq.error "Hole level not found".

pred find_goal i:list prop, o:term.
find_goal [def _ N _ (app [GG, G]) | _ ] G :- 
  coq.name->id N "PrevGoal", 
  get_name "Goal" GG, !,
  coq.say "yay goal".
find_goal [_|PS] G :- /* coq.say P, */ find_goal PS G.
find_goal [] _ :-  coq.error "Previous goal not found".

pred find_file i:list prop, o:term.
find_file [def _ N _ (app [FN, F]) | _ ] F :- 
  coq.name->id N "OutFileName", 
  get_name "FileName" FN, !,
  coq.say "yay file".
find_file [_|PS] F :- /* coq.say P, */ find_file PS F.
find_file [] _ :-  coq.error "Out file not found".

pred find_out_translation i:list prop, o:term, o:term.
find_out_translation [def X N _ (app [FN, F]) | _ ] X F :- 
  coq.name->id N "OutTranslation", 
  get_name "Translation" FN, !,
  coq.say "yay translation".
find_out_translation [_|PS] X F :- /* coq.say P, */ find_out_translation PS X F.
find_out_translation [] _ _ :-  coq.error "Out translation not found".

pred nat->int i:term, o:int.
nat->int (app [S,K]) N :- 
  get_name "S" S,
  nat->int K KI,
  N is (KI + 1).
nat->int O 0 :- get_name "O" O.

pred coqlist->list i:term, o:list term.
coqlist->list (app [Cons, _, X, XS]) L :-
  get_name "List.cons" Cons,
  coqlist->list XS L1,
  L = [X|L1].
coqlist->list (app [Nil,_] ) [] :- get_name "List.nil" Nil.

pred listint->string i:list int, o:string.
listint->string [N|NS] SS :- 
  listint->string NS S,
  SS is S ^ "." ^ (int_to_string N).
listint->string [] "" .  

pred translate_hole i:term, i:goal-ctx, i:int, o:int, o:string.
translate_hole T Ctx HoleId NewHoleId HoleS :- 
    find_level Ctx Lvl,
    coqlist->list Lvl LvlL,
    std.map LvlL nat->int LvlLI,
    listint->string [HoleId|LvlLI] LvlS,
    (NewHoleId is HoleId + 1),
    HoleS is "Hole" ^ LvlS. /* Hole.1.2.3.1 */

pred translate_apply_pure  i:term, i:goal-ctx, i:int, o:int, o:string.
translate_apply_pure (app [T|Args]) Ctx HoleId NewHoleId SS  :- 
  get_name "Build_XUBInteger" PF,
  std.rev Args [app [PF|_] | [URV | _] ], !,
  translate_rvalue URV Ctx HoleId NewHoleId SS.
translate_apply_pure X _ _ _ _ :- coq.error "translate_apply_pure: not implemented:" X.

pred translate_urstate  i:term, i:goal-ctx, i:int, o:int, o:string.
translate_urstate (app [T|Args]) Ctx HoleId HoleId ""  :- 
  coq.say Args.

pred translate_rglobal i:gref, o:string.
translate_rglobal IT OS :-
  (IT = const ITC),
  std.any->string ITC IS,
  (K is size IS),
  (P is substring IS (K - 8) 6),
  (P = "_right"),
  (OS is substring IS 2 (K - 10)).
translate_rglobal IT OS :-
  std.any->string IT OS.


pred translate_lglobal i:gref, o:string.
translate_lglobal IT OS :-
  (IT = const ITC),
  std.any->string ITC IS,
  (K is size IS),
  (P is substring IS (K - 7) 5),
  (P = "_left"),
  (OS is substring IS 2 (K - 9)).
translate_lglobal IT OS :-
  std.any->string IT OS.


pred translate_rvalue i:term, i:goal-ctx, i:int, o:int, o:string.
translate_rvalue T Ctx HoleId NewHoleId SS  :- 
  is_hole T, !,
  coq.say "translate_rvalue RHole" T,
  coq.say "RHole" ,
  translate_hole T Ctx HoleId NewHoleId SS , !.
translate_rvalue T Ctx HoleId NewHoleId SS :- 
  (get_name "URScalar" URS; get_name "sInjectL" URS),
  (T = app [URS|_]), !, 
  coq.say "URScalar" ,
  translate_urscalar T Ctx HoleId NewHoleId SS. 
translate_rvalue T Ctx HoleId NewHoleId SS :- 
  get_name "ULtoRValueL" ULRV,
  (T = app [ULRV|_]), !,
  coq.say "translate_rvalue ULtoRValueL",
  coq.say "ULtoRValueL" , 
  translate_ultorvalue T Ctx HoleId NewHoleId SS.
translate_rvalue T Ctx HoleId NewHoleId SS :- 
  get_name "wrapURValueL" WURV,
  (T = app [WURV|_]), !,
  coq.say "translate_rvalue wrapURValueL" ,
  translate_wrapurvalue T Ctx HoleId NewHoleId SS. 
translate_rvalue T Ctx HoleId NewHoleId SS :- 
  get_name "apply_pure" APP,
  (T = app [APP|_]), !,
  coq.say "translate_rvalue apply_pure",
  translate_apply_pure T Ctx HoleId NewHoleId SS.
translate_rvalue T Ctx HoleId NewHoleId SS :- 
  get_name "URState" URS,
  (T = app [URS|Args]),
  coq.say "translate_rvalue urstate",
  translate_urstate T Ctx HoleId NewHoleId SS.
translate_rvalue T Ctx HoleId HoleId SS  :-
  find_ctx_var T Ctx SS.
translate_rvalue T Ctx HoleId HoleId SS :- 
  coq.say "translate_rvalue global",
  (T = global TG),
  translate_rglobal TG SS.
translate_rvalue T _ _ _ _ :- coq.error "translate_rvalue: not implemented" T.

pred translate_lvalue i:term, i:goal-ctx, i:int, o:int, o:string.
translate_lvalue T Ctx HoleId NewHoleId SS :- 
  is_hole T,
  translate_hole T Ctx HoleId NewHoleId SS.
translate_lvalue T Ctx HoleId HoleId SS  :-
  find_ctx_var T Ctx SS.
translate_lvalue T Ctx HoleId HoleId SS :- 
  coq.say "translate_lvalue global",
  (T = global TG),
  translate_lglobal TG SS.
translate_lvalue T Ctx HoleId HoleId SS  :-
  coq.error "translate_lvalue: not implemented: " T.
/* expressions */

pred translate_if i:term, i:goal-ctx, i:int, o:int, o:string.
translate_if (app L) Ctx HoleId NewHoleId3 SS  :- 
  std.rev L [Else | [Then | [Cond | _ ]]],
  translate_rvalue Cond Ctx HoleId NewHoleId CondS,
  translate_expression Then Ctx NewHoleId NewHoleId2 ThenS,
  translate_expression Else Ctx NewHoleId2 NewHoleId3 ElseS,
  SS is "if ( " ^ CondS ^ " ) {\n" ^ ThenS ^ "} else {\n" ^ ElseS ^ "}".                                                                                                              
translate_if _ _ _ _ _ :- coq.error "Error in translate_if".

pred translate_require i:term, i:goal-ctx,  i:int, o:int, o:string.
translate_require (app L) Ctx HoleId NewHoleId2 SS  :- std.rev L [ECode | [Cond | _]],
                                     translate_rvalue Cond Ctx HoleId NewHoleId CondS,
                                     translate_rvalue ECode Ctx NewHoleId NewHoleId2 ECodeS,
                                     SS is "require ( " ^ CondS ^ ", " ^ ECodeS ^ " )".
translate_require _ _ _ _ _ :- coq.error "Error in translate_require".

pred translate_assign i:term, i:goal-ctx, i:int, o:int, o:string.
translate_assign (app L) Ctx HoleId NewHoleId2 SS  :-  std.rev L [RHS | [LHS | _]],
                                     translate_lvalue LHS Ctx HoleId NewHoleId LHSS, 
                                     translate_rvalue RHS Ctx NewHoleId NewHoleId2 RHSS,
                                     (RHSS = "$Default$", SS is "";  SS is LHSS ^ " = " ^ RHSS). 
translate_assign _ _ _ _ _ :- coq.error "Error in translate_assign".

pred translate_return i:term, i:goal-ctx, i:int, o:int, o:string.
translate_return (app L) Ctx HoleId NewHoleId SS  :-  std.rev L [RV | _],
                                     translate_rvalue RV Ctx HoleId NewHoleId RVSS,
                                     SS is "return " ^ RVSS.
translate_return _ _ _ _ _ :- coq.error "Error in translate_return".

pred translate_binding i:term, i:goal-ctx, i:int, o:int, o:string.
translate_binding (app L) Ctx HoleId NewHoleId2 SS  :-  std.rev L [SB | [FB | _]],
                                     translate_expression FB Ctx HoleId NewHoleId FBS,
                                     translate_expression SB Ctx NewHoleId NewHoleId2 SBS,
                                     (FBS = "", SS is "\n" ^ SBS; SS is FBS ^ ";\n" ^ SBS).

pred translate_dynbinding i:term, i:goal-ctx, i:int, o:int, o:string.
translate_dynbinding (app L) Ctx HoleId NewHoleId SS  :-  std.rev L [F | [LedgerT | _]],
                                     /* coq.say "F = " F, */
                                     (F = fun Name Ty x \ Expr x),
                                     (pi x \ translate_expression (Expr x) [decl x Name Ty | Ctx] HoleId NewHoleId ExprS ),
                                     translate_ultype Ty TyS, 
                                     coq.name->id Name NameS,
                                     SS is TyS ^ " " ^ NameS ^ "; " ^ ExprS
                                     /* translate_expression FB Ctx HoleId NewHoleId FBS,
                                     translate_expression SB Ctx NewHoleId NewHoleId2 SBS, */
                                     /* SS is FBS ^ ";\n" ^ SBS */.    
pred translate_ulexpression i:term, i:goal-ctx, i:int, o:int, o:string.
translate_ulexpression (app L) Ctx HoleId HoleId SS :- std.rev L [Exp | [H | _]], 
                                        coq.say "Exp=" Exp,
                                        coq.say "H=" H,
                                        SS is "".                                                                  

pred translate_pure_type i:term, o:string. 
translate_pure_type T S :- 
get_name "XBool" T, 
S is "bool". 
translate_pure_type T S :- 
get_name "XInteger" T,
S is "int".
translate_pure_type T S :- 
get_name "XUInteger8" T,
S is "uint8".
translate_pure_type T S :- 
get_name "XUInteger16" T,
S is "uint16".
translate_pure_type T S :- 
get_name "XUInteger32" T,
S is "uint32".
translate_pure_type T S :- 
get_name "XUInteger64" T,
S is "uint64".
translate_pure_type T S :- 
get_name "XUInteger128" T,
S is "uint128".
translate_pure_type T S :- 
get_name "XUInteger256" T,
S is "uint256".
translate_pure_type T S :- 
get_name "XUInteger" T,
S is "uint".
translate_pure_type T S :- 
get_name "cell" T,
S is "TvmCell".
translate_pure_type T S :- 
get_name "builder" T,
S is "TvmBuilder".
translate_pure_type T S :- 
get_name "slice" T,
S is "TvmSlice".

translate_pure_type (app [F , K , V]) S :-
  get_name "XHMap" F, 
  translate_pure_type K KS,
  translate_pure_type V VS,
  S is "mapping (" ^ KS ^ " => " ^ VS ^ ")".
translate_pure_type (app [F , K ]) S :-
  get_name "XMaybe" F, 
  translate_pure_type K KS,
  S is "optional (" ^ KS ^ ")".
translate_pure_type (app [F , X , Y ]) S :-
  get_name "XProd" F, 
  translate_pure_type X XS,
  translate_pure_type Y YS,
  S is "(" ^ XS ^ ", " ^ YS ^ ")".

translate_pure_type T _ :- coq.error "translate_pure_type: not implemented" T.


pred translate_ultype i:term, o:string.
translate_ultype (app [ULV|Args]) S :-
get_name "ULValueL" ULV,
std.rev Args [T|_],
translate_pure_type T S.
translate_ultype T _ :- coq.error "translate_ultype: not implemented" T.

pred translate_func_name i:string, o:string.
translate_func_name "@tvm_accept_left" "tvm.accept".
translate_func_name "@tvm_rawReserve_left" "tvm.rawReserve".
translate_func_name "@tvm_setCurrentCode_left" "tvm.setCurrentCode" .
translate_func_name "@tvm_setCode_left" "tvm.setcode" .
translate_func_name "@tvm_resetStorage_left" "tvm.resetStorage" .
translate_func_name "@tvm_transfer_left" ".transfer" .
translate_func_name "@suicide_left" "selfdestruct" .
translate_func_name "@storeRef" "storeRef" .
translate_func_name "@builder_assign_left" "store" .

translate_func_name "@plusassign_left"  " += ".
translate_func_name "@minusassign_left" " -= ".
translate_func_name "@andassign_left"   " &= ".
translate_func_name "@orassign_left"    " |= ".

translate_func_name "@incr_post_left"   " ++ ".
translate_func_name "@decr_post_left"   " -- ".
translate_func_name "@incr_pre_left"    " ++ ".
translate_func_name "@decr_pre_left"    " -- ".

translate_func_name FS _ :- coq.error "translate_func_name: not implemeneted: " FS.


pred translate_rvalue_list i:list term, i:list implicit_kind, i:goal-ctx, i:int, o:int, i:string, o:string.
translate_rvalue_list [A | Args] [explicit | ArgL] Ctx HoleId NewHoleId2 Acc ArgSS :-
  translate_rvalue A Ctx HoleId NewHoleId ArgS,
  coq.say "ArgS@ = " ArgS,
  ((Acc = "", NewAcc is ArgS); NewAcc is Acc ^ ", " ^ ArgS),
  coq.say "NewAcc=" NewAcc,
  translate_rvalue_list Args ArgL Ctx NewHoleId NewHoleId2 NewAcc ArgSS.

translate_rvalue_list [_ | Args] [_ | ArgL] Ctx HoleId NewHoleId Acc ArgS :-
  translate_rvalue_list Args ArgL Ctx HoleId NewHoleId Acc ArgS.
translate_rvalue_list [] [_|_] _ _ _ _ _ :- coq.error "different number of arguments".
translate_rvalue_list [_|_] [] _ _ _ _ _ :- coq.error "different number of arguments".

translate_rvalue_list [] [] _ HoleId HoleId Acc Acc :- coq.say "Acc@=" Acc.


pred translate_lvalue_arg i:list term, i:list implicit_kind, i:goal-ctx, i:int, o:int, o:string.
translate_lvalue_arg [A | Args] [explicit | ArgL] Ctx HoleId NewHoleId ArgS :-
  translate_lvalue A Ctx HoleId NewHoleId ArgS,
  coq.say "ArgS@ = " ArgS.

translate_lvalue_arg [_ | Args] [_ | ArgL] Ctx HoleId NewHoleId ArgS :-
  translate_lvalue_arg Args ArgL Ctx HoleId NewHoleId ArgS.






pred translate_rvalue_list1 i:list term, i:list implicit_kind, i:goal-ctx, i:int, o:int, i:string, o:string, o:string.
translate_rvalue_list1 [A | Args] [explicit | ArgL] Ctx HoleId NewHoleId2 Acc ArgS1 ArgSS :-
  translate_rvalue A Ctx HoleId NewHoleId ArgS1,
  coq.say "ArgS1 = " ArgS1,
  translate_rvalue_list Args ArgL Ctx NewHoleId NewHoleId2 Acc ArgSS.

translate_rvalue_list1 [_ | Args] [_ | ArgL] Ctx HoleId NewHoleId Acc ArgS1 ArgS :-
  translate_rvalue_list1 Args ArgL Ctx HoleId NewHoleId Acc ArgS1 ArgS.

translate_rvalue_list1 _ _ _ _ _ _ _ _ :- coq.error "dont first arg" .

   
pred translate_rvalue_list1o2 i:list term, i:list implicit_kind, i:goal-ctx, i:int, o:int, i:string, o:string, o:string.
translate_rvalue_list1o2 L [explicit | ArgL] Ctx HoleId NewHoleId2 Acc ArgS1 ArgS2  :-
std.rev L [AA | [A | Args]] ,
coq.say "A=" A,
coq.say "AA=" AA,
  translate_lvalue A Ctx HoleId NewHoleId ArgS1,
  coq.say "ArgS1 = " ArgS1,
  translate_rvalue AA Ctx NewHoleId NewHoleId2 ArgS2, 
  coq.say "ArgS2 = " ArgS2.

translate_rvalue_list1o2 [_ | Args] [_ | ArgL] Ctx HoleId NewHoleId Acc ArgS1 ArgS2  :-
coq.say "_ Args =" Args,
  translate_rvalue_list1o2 Args ArgL Ctx HoleId NewHoleId Acc ArgS1 ArgS2 .

translate_rvalue_list1o2 [_ | [ _ | Args]] [_ | ArgL] Ctx HoleId NewHoleId Acc ArgS1 ArgS2  :-
coq.say "_ _ Args =" Args ,
  translate_rvalue_list1o2 Args ArgL Ctx HoleId NewHoleId Acc ArgS1 ArgS2 .

translate_rvalue_list1o2 _ _ _ _ _ _ _ _  :- coq.error "dont first or second args" .
   


pred first_argum_before_funname i:string.
first_argum_before_funname Fn :- Fn = "@tvm_transfer_left".

pred infix_operators i:string.
infix_operators Fn :- Fn = "@plusassign_left".
infix_operators Fn :- Fn = "@minusassign_left".
infix_operators Fn :- Fn = "@andassign_left".
infix_operators Fn :- Fn = "@orassign_left".

pred postfix_operators i:string.
postfix_operators Fn :- Fn = "@incr_post_left".
postfix_operators Fn :- Fn = "@decr_post_left".

pred prefix_operators i:string.
prefix_operators Fn :- Fn = "@incr_pre_left".
prefix_operators Fn :- Fn = "@decr_pre_left".

pred translate_expression i:term, i:goal-ctx, i:int, o:int, o:string.
translate_expression  T Ctx HoleId NewHoleId ExprS  :- 
  is_hole T,
  coq.say "Hole found",
  translate_hole T Ctx HoleId NewHoleId ExprS, !.
translate_expression  (app [If|_] as T) Ctx HoleId NewHoleId ExprS  :- 
  get_name "IfElseExpression" If,
  translate_if T Ctx HoleId NewHoleId ExprSS,
  (ExprS is ExprSS /* ^ ";" */), !.
translate_expression  (app [Req|_] as T) Ctx HoleId NewHoleId ExprS :- 
  get_name "RequireExpression" Req,
  translate_require T Ctx HoleId NewHoleId ExprSS,
  (ExprS is ExprSS /* ^ ";" */), !.
translate_expression  (app [Ass|_] as T) Ctx HoleId NewHoleId ExprS :- 
  get_name "AssignExpression" Ass,
  translate_assign T Ctx HoleId NewHoleId ExprSS,
  (ExprS is ExprSS /* ^ ";" */), !.  
translate_expression  (app [Ret|_] as T) Ctx HoleId NewHoleId ExprS :- 
  get_name "ReturnExpression" Ret,
  translate_return T Ctx HoleId NewHoleId ExprSS,
  (ExprS is ExprSS /* ^ ";" */), !.
translate_expression  (app [Bind|_] as T) Ctx HoleId NewHoleId ExprS :- 
  get_name "StrictBinding" Bind,
  translate_binding T Ctx HoleId NewHoleId ExprSS,
  (ExprS is ExprSS /* ^ ";" */), !.      
translate_expression  (app [DBind|_] as T) Ctx HoleId NewHoleId ExprS :- 
  get_name "DynamicBinding" DBind,
  translate_dynbinding T Ctx HoleId NewHoleId ExprSS,
  (ExprS is ExprSS /* ^ ";" */), !.
translate_expression  (app [WULE|_] as T) Ctx HoleId NewHoleId ExprS :- 
  get_name "wrapULExpression" WULE,
  translate_ulexpression T Ctx HoleId NewHoleId ExprSS,
  (ExprS is ExprSS /* ^ ";" */), !.
translate_expression (app [F|Args] as T) Ctx HoleId NewHoleId ExprS :- 
  coq.term->string F FS,
coq.say "Args=" Args,
  (F = global FG),
  coq.arguments.implicit FG [ArgL],
  coq.say "FS=" FS,
  translate_func_name FS FSS,
 (
    (
      prefix_operators FS ,
      translate_lvalue_arg Args ArgL Ctx HoleId NewHoleId ArgS,
      (ExprS is FSS ^ ArgS )  
    );
    (
      postfix_operators FS ,
      translate_lvalue_arg Args ArgL Ctx HoleId NewHoleId ArgS,
      (ExprS is ArgS ^ FSS )  
    );
    (
      infix_operators FS ,
      translate_rvalue_list1o2 Args ArgL Ctx HoleId NewHoleId "" ArgS1 ArgS2 ,
      (ExprS is ArgS1 ^ FSS ^ ArgS2)  
    );
    ( 
      first_argum_before_funname FS , 
      translate_rvalue_list1 Args ArgL Ctx HoleId NewHoleId "" ArgS1 ArgS,
      (ExprS is ArgS1 ^ FSS ^ "(" ^ ArgS ^ ")")  
    );
    (
      translate_rvalue_list Args ArgL Ctx HoleId NewHoleId "" ArgS,
      (ExprS is FSS ^ "(" ^ ArgS ^ ")")
    )
 ).
translate_expression  T _ _ _ _  :- 
  coq.error "translate_expression: not implemented: " T.

pred not-hyp i:term, i:prop, o:term.
  not-hyp X (decl Y _ Ty) Y :- not (occurs X Ty), not (X = Y).
  not-hyp X (def Y _ Ty Bo) Y :- not (occurs X Ty ; occurs X Bo), not (X = Y).

pred not-hyp2 i:term, i:prop, o:prop.
not-hyp2 X (decl Y N Ty) (decl Y N Ty) :- not (occurs X Ty), not (X = Y).
not-hyp2 X (def Y N Ty Bo) (def Y N Ty Bo) :- not (occurs X Ty ; occurs X Bo), not (X = Y).

pred find_ctx_var_by_name i:string, i:list prop, o:term.
find_ctx_var_by_name IN [def X N _ _ | _ ] X :- 
  coq.name->id N IN.
find_ctx_var_by_name IN [_P|PS] X :- /* coq.say P, */ find_ctx_var_by_name IN PS X.
find_ctx_var_by_name _ [] _ :-  coq.error "Term not found".

type clear-var string -> open-tactic.
clear-var N (goal Ctx R T E Args) [seal (goal Ctx1 E1 T E [])] :-
  find_ctx_var_by_name N Ctx X,
  coq.say "Found term:" X,
  name X, !, std.do! [
  std.map-filter Ctx (not-hyp X) VisibleRev,
  std.map-filter Ctx (not-hyp2 X) VisibleCtx,
  prune E1 {std.rev VisibleRev},
  std.rev VisibleCtx Ctx1,
  std.assert-ok! (coq.typecheck E1 T) "cannot clear",
  E = E1 ].
clear-var N _ _ :- coq.error "Cannot clear var:" N.

type set-var string -> term -> open-tactic.
set-var N V (goal Ctx R T E _ as G) GS :- 
  std.assert! (coq.ltac.id-free? N G) "name already taken",
  coq.id->name N NN,
  refine (let NN _ V _) G GS.
set-var N _ _ _ :- coq.error "Cannot set var:" N.

pred solve_common i:term, 
                  i:string, 
                  i:string, 
                  i:string, 
                  i:(term -> goal-ctx -> int -> int -> string -> prop), 
                  i:goal-ctx,
                  o:term,
                  o:string.
solve_common Expr N _FN Footer TF Ctx OutTrm OutSSS :- 
    find_level Ctx Lvl,
    /* coq.say Lvl, */
    coqlist->list Lvl LvlL ,
    LL is {std.length LvlL},
    (LL = 1), !,
    coq.say "translating"  N  "...",
    find_out_translation Ctx OutTrm Out,
    coq.term->string Out OutS,
    (K is size OutS),
    ((K =< 2, OutSS is ""); OutSS is substring OutS 1 (K - 2)),
    TF Expr Ctx 0 _ ExprS,
    (ExprS = "", ExprSS is ""; ExprSS is ExprS ^ Footer),
    OutSSS is OutSS ^ ExprSS.
solve_common Expr N _FN _ TF Ctx OutTrm OutSSS :- 
    coq.say "translating"  N  "in hole ...",
    TF Expr Ctx 0 _ ExprS,
    find_level Ctx Lvl,
    coqlist->list Lvl LvlL,
    std.map LvlL nat->int LvlLI,
    listint->string LvlLI LvlS,
    LvlSS is "Hole" ^ LvlS,
    find_out_translation Ctx OutTrm Out,
    coq.term->string Out OutS,
    (K is size OutS),
    ((K =< 2, OutSS is ""); OutSS is substring OutS 1 (K - 2)),
    split_string "" LvlSS OutSS SL,
    join ExprS SL OutSSS.

type idtac open-tactic.
idtac  G [seal G].  

}}.

Elpi Tactic bk_translate.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db string_utils.
Elpi Accumulate Db bk_translate_utils.

Elpi Accumulate lp:{{

type solve open-tactic.
solve (goal Ctx _ _GoalType _ [trm Expr] as G) GS :-
  find_goal Ctx PG, 
  get_name "URValueP"  URVP,
  get_name "URValueL"  URVL,
  ( PG =  app [URVL | _] ; PG =  app [URVP | _]), 
  !,
  /* coq.say Expr , */
  solve_common Expr "URValue" _FNSS "" translate_rvalue Ctx _OutTrm OutS,
  get_name "Translation" Tr,
  coq.string->term OutS OutSTerm,
  coq.ltac.thenl [ coq.ltac.open (clear-var "OutTranslation") , 
                   coq.ltac.open (set-var  "OutTranslation" {{lp:Tr lp:OutSTerm}}) ] (seal G) GS.
solve  (goal Ctx _ _GoalType _ [trm Expr] as G) GS :-
  find_goal Ctx PG, 
  get_name "ULValueP"  ULVP,
  get_name "ULValueL"  ULVL,
  ( PG =  app [ULVL | _] ; PG =  app [ULVP | _]  ), 
  !,
  /* coq.say Expr , */
  solve_common Expr "ULValue" _FNSS "" translate_lvalue Ctx _OutTrm OutS,
  get_name "Translation" Tr,
  coq.string->term OutS OutSTerm,
  coq.ltac.thenl [ coq.ltac.open (clear-var "OutTranslation") , 
                   coq.ltac.open (set-var  "OutTranslation" {{lp:Tr lp:OutSTerm}}) ] (seal G) GS.


solve  (goal Ctx _ _GoalType _ [trm Expr] as G) GS :-
  find_goal Ctx PG, 
coq.say "translate_expression",
  get_name "UExpressionP" UExp,
coq.say "UExpressionP" UExp,
  get_name "public" Pub,
coq.say "public" Pub,
  get_name "external" Ext,
coq.say "external" Ext,
  ( PG =  app [UExp | _] ; PG = app [Pub | _] ; PG = app [Ext | _] ), 
  !,
  /* coq.say Expr , */
  solve_common Expr "UExpression" _FNSS "" translate_expression Ctx _OutTrm OutS,
  get_name "Translation" Tr,
  coq.string->term OutS OutSTerm,
  coq.ltac.thenl [ coq.ltac.open (clear-var "OutTranslation") , 
                   coq.ltac.open (set-var "OutTranslation" {{lp:Tr lp:OutSTerm}}) ] (seal G) GS. 
}}.
  
Elpi Typecheck.

Elpi Tactic fin.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db bk_translate_utils.
Elpi Accumulate Db string_utils.

Elpi Accumulate lp:{{

type set-solution term -> term -> open-tactic.
set-solution T Out (goal Ctx T Ty E _Arg )
               [seal (goal Ctx T Ty E [trm Out])].
set-solution _ _ _ _ :- coq.error "cannot set solution". 

type solve1 open-tactic.
solve1 (goal Ctx _ GoalType _ [trm Expr] as G) GS :-
  (PG = GoalType), 
  get_name "URValueP"  URVP,
  get_name "URValueL"  URVL,
  ( PG =  app [URVL | _] ; PG =  app [URVP | _]), 
  !,
  /* coq.say Expr , */
  solve_common Expr "URValue" _FNSS "" translate_rvalue Ctx _OutTrm OutS,
  get_name "Translation" Tr,
  coq.string->term OutS OutSTerm,
  coq.ltac.open (set-solution Expr {{lp:Tr lp:OutSTerm}}) (seal G) GS .

solve1  (goal Ctx _ GoalType _ [trm Expr] as G) GS :-
  (PG = GoalType), 
  get_name "ULValueP"  ULVP,
  get_name "ULValueL"  ULVL,
  ( PG =  app [ULVL | _] ; PG =  app [ULVP | _]  ), 
  !,
  /* coq.say Expr , */
  solve_common Expr "ULValue" _FNSS "" translate_lvalue Ctx _OutTrm OutS,
  get_name "Translation" Tr,
  coq.string->term OutS OutSTerm,
  coq.ltac.open (set-solution Expr {{lp:Tr lp:OutSTerm}}) (seal G) GS .

solve1  (goal Ctx _ GoalType _ [trm Expr] as G) GS :-
  (PG = GoalType), 
  get_name "UExpressionP" UExp,
  get_name "public" Pub,
  ( PG =  app [UExp | _] ; PG = app [Pub | _] ), 
  !,
  /* coq.say Expr , */
  solve_common Expr "UExpression" _FNSS "" translate_expression Ctx _OutTrm OutS,
  get_name "Translation" Tr,
  coq.string->term OutS OutSTerm,
  coq.ltac.open (set-solution Expr {{lp:Tr lp:OutSTerm}}) (seal G) GS .

pred find_out_translation_with_nablas i:sealed-goal, o:term.
find_out_translation_with_nablas (nabla G) S :-
  (pi x\ find_out_translation_with_nablas (G x) S).
find_out_translation_with_nablas (seal (goal Ctx _ _ _ _)) S :- 
  find_out_translation Ctx _ S.

pred find_file_with_nablas i:sealed-goal, o:term.
find_file_with_nablas (nabla G) S :-
  (pi x\ find_file_with_nablas (G x) S).
find_file_with_nablas (seal (goal Ctx _ _ _ _)) S :- 
  find_file Ctx S.

pred find_arg_with_nablas i:sealed-goal, o:term, o:term.
find_arg_with_nablas (nabla G) S Ty:-
  (pi x\ find_arg_with_nablas (G x) S Ty).
find_arg_with_nablas (seal (goal _ _ Ty _ [trm S])) S Ty:-!.

pred find_arg_with_nablas1 i:sealed-goal, o:term.
find_arg_with_nablas1 (nabla G) S :-
  (pi x\ find_arg_with_nablas1 (G x) S ).
find_arg_with_nablas1 (seal (goal _ _ _ _ [trm S])) S :-!.

type clear-set string -> term -> open-tactic.
clear-set N T (goal _ _ _ _ _ as G) GS :-
  clear-var N G [seal G1],
  set-var N T G1 GS.

pred write_to_file i:sealed-goal, i:term.
write_to_file SG T :-
  find_file_with_nablas SG FN,
  /* coq.say FN, */
  coq.term->string FN FNS,
  (K is size FNS),
  K > 2, 
  FNSS is substring FNS 1 (K - 2),
  coq.term->string T TS,
  (M is size TS),
  TSS is substring TS 1 (M - 2),
  open_out FNSS OS,
  output OS TSS,
  flush OS, 
  close_out OS.
write_to_file _ _ :- coq.error "Something wrong with file".

msolve [G|GX] GS :- 
  coq.ltac.open solve1 G [G1],
  find_arg_with_nablas1 G1 Out, 
  coq.ltac.all (coq.ltac.open (clear-set "OutTranslation" Out )) GX GS,
  (Out = app [_ , OutS]),
  if (GX = []) (coq.say "no more goals" /* , write_to_file G OutS */ ) true.

msolve _ _ :- coq.error "Cannot finish current goal".  

}}.

Elpi Typecheck.

About new_lvalue.

(* (DynamicBinding (new_lvalue b)
             (fun x: ULValue ty => StrictBinding (AssignExpression x r) f ) ) *)


Elpi Tactic refine_new.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db string_utils.

Elpi Accumulate lp:{{

pred fix_new i:term, o:term.
fix_new (app [DynamicBinding|XS]) Out :-
  get_name "DynamicBinding" DynamicBinding,
  std.rev XS [F , NL | YS],
  (F = fun Name Ty x \ Expr x),
  (NL = app NLL),
  std.rev NLL [_|NLLR],
  coq.name->id Name NameS,
  coq.string->term NameS NameSS,
  std.rev [NameSS|NLLR] NLLRR,
  (Out = app [DynamicBinding|XXS]),
  std.map YS fix_new YYS,
  std.rev [F , app NLLRR | YYS] XXS.
fix_new (app [T|XS]) Out :- 
  (Out = app [{fix_new T}|YS]),
  std.map XS fix_new  YS.
fix_new T T.

solve  (goal _Ctx _ _GoalType _ [trm Expr] as G) GS :-
  fix_new Expr Expr1,
  refine Expr1 G GS.

}}.

Elpi Typecheck.



Inductive IGoal      : Type := | Goal : Type -> IGoal.
Inductive IHoleLevel : Set  := | HoleLevel: List.list nat -> IHoleLevel.
Inductive IFileName  : Set  := | FileName: string -> IFileName.
Inductive ITranslation  : Set  := | Translation: string -> ITranslation.


Tactic Notation "begin" uconstr(s)  := ( set (PrevGoal:=Goal False);
                                         set (HLevel:=HoleLevel (List.cons 0%nat List.nil)) ;
                                         set (OutFileName:=FileName s);
                                         set (OutTranslation:=Translation "") (* ;
                                         elpi clear_file (s) *) ).


Elpi Tactic PrefixTest.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db bk_translate_utils.
Elpi Accumulate Db string_utils.

Elpi Accumulate lp:{{

/* type set-var string -> term -> open-tactic.
set-var N V (goal _Ctx _R _T _E _ as G) GS :- 
  std.assert! (coq.ltac.id-free? N G) "name already taken",
  coq.id->name N NN,
  refine (let NN _ V _) G GS.
set-var N _ _ _ :- coq.error "Cannot set var:" N. */

solve (goal _ _ _ _ [str Name] as G) GL :- 
    attributes A,
    coq.say A,
    (FName is Name ^ ".sol"),
    coq.string->term FName FNameS,
    coq.ltac.open (set-var "PrevGoal" {{ Goal False }}) (seal G) [G1],
    coq.ltac.open (set-var "HLevel" {{ HoleLevel (List.cons 0%nat List.nil) }}) G1 [G2],
    coq.ltac.open (set-var "OutFileName" {{ FileName lp:FNameS }}) G2 [G3],
    coq.ltac.open (set-var "OutTranslation" {{ Translation "" }}) G3 GL /* ,
    open_out FName OS,
    flush OS, 
    close_out OS */.
}}.

Elpi Typecheck.

Global Set UrsusPrefixTactic "PrefixTest". 


(* Elpi Command UrsusDefined.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db string_utils.

Elpi Accumulate lp:{{

main [str F] :-
  coq.say F,
  get_name F FT,
  coq.say FT,
  attributes A,
  coq.say A.

}}.

Elpi Typecheck.

Global Set UrsusDefault "UrsusDefined". *)


Tactic Notation "!" uconstr(s) := (match goal with
                                   | PrevGoal := Goal _ |- ?G => clear PrevGoal; set (PrevGoal:=Goal G)
                                   | |- ?G=> set (PrevGoal:=Goal G)
                                   end ; refine s).
Tactic Notation "!0" uconstr(s) := ( match goal with
                                             | PrevGoal := Goal _ |- ?G => clear PrevGoal; set (PrevGoal:=Goal G)
                                             | |- ?G => set (PrevGoal:=Goal G)
                                             end ; 
                                     elpi bk_translate (s); 
                                     refine s).
Tactic Notation "!1" uconstr(s) := ( !s; [] ;
                                         [ elpi bk_translate (s); 
                                          match goal with
                                          | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (0%nat::L)%list)
                                          end ] ).
Tactic Notation "!2" uconstr(s) := ( !s; [|];
                                     [ elpi bk_translate (s); match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel  (0%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (1%nat::L)%list)
                                       end] ).
Tactic Notation "!3" uconstr(s) := ( !s; [ | | ];
                                     [ elpi bk_translate (s); match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (0%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (1%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (2%nat::L)%list)
                                       end] ).    
Tactic Notation "!4" uconstr(s) := ( !s; [ | | | ];
                                     [ elpi bk_translate (s); match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (0%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (1%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (2%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (3%nat::L)%list)
                                       end] ).    
Tactic Notation "!5" uconstr(s) := ( !s; [ | | | | ];
                                     [ elpi bk_translate (s); match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (0%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (1%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (2%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (3%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (4%nat::L)%list)
                                       end] ). 


Tactic Notation "?!" uconstr(s) := (match goal with
                                   | PrevGoal := Goal _ |- ?G => clear PrevGoal; set (PrevGoal:=Goal G)
                                   | |- ?G=> set (PrevGoal:=Goal G)
                                   end ; elpi refine_new (s)).
Tactic Notation "?!0" uconstr(s) := ( match goal with
                                             | PrevGoal := Goal _ |- ?G => clear PrevGoal; set (PrevGoal:=Goal G)
                                             | |- ?G => set (PrevGoal:=Goal G)
                                             end ; 
                                     elpi bk_translate (s); 
                                     elpi refine_new (s)).
Tactic Notation "?!1" uconstr(s) := ( ?!s; [] ;
                                         [ elpi bk_translate (s); 
                                          match goal with
                                          | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (0%nat::L)%list)
                                          end ] ).
Tactic Notation "?!2" uconstr(s) := ( ?!s; [|];
                                     [ elpi bk_translate (s); match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel  (0%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (1%nat::L)%list)
                                       end] ).
Tactic Notation "?!3" uconstr(s) := ( ?!s; [ | | ];
                                     [ elpi bk_translate (s); match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (0%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (1%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (2%nat::L)%list)
                                       end] ).    
Tactic Notation "?!4" uconstr(s) := ( ?!s; [ | | | ];
                                     [ elpi bk_translate (s); match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (0%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (1%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (2%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (3%nat::L)%list)
                                       end] ).    
Tactic Notation "?!5" uconstr(s) := ( ?!s; [ | | | | ];
                                     [ elpi bk_translate (s); match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (0%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (1%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (2%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (3%nat::L)%list)
                                       end | match goal with
                                       | l:=HoleLevel ?L |- _ => clear l; set (HLevel:=HoleLevel (4%nat::L)%list)
                                       end] ). 


Tactic Notation "vararg" ident(x) constr(ss) := 
let s := fresh x in 
let T := type of x in 
refine {{new 'x : T @ ss := {} ; {_} }} ;
refine {{ {x} := #{s} ; {_} }} ;
clear s.

Tactic Notation ":" uconstr(s)  := first [  !1 s | !2 s |  !3 s |  !4 s |  !5 s | !0 s ].
Tactic Notation "?:" uconstr(s)  := first [  ?!1 s | ?!2 s |  ?!3 s |  ?!4 s |  ?!5 s | ?!0 s ].
Notation " // e " := {{ {e} ; {_} }} (at level 0, e custom ULValue at level 20, only parsing).
Notation " || e " := e (at level 0, e custom URValue at level 20,  only parsing).
Notation " // e | " := e (at level 0, e custom ULValue at level 20,  only parsing).
Notation "'_'" := _ (in custom URValue at level 0,  only parsing).
Notation "'_'" := _ (in custom ULValue at level 0,  only parsing).
(* Notation "e" := e (in custom URValue at level 0, e bigint). *)
Notation "e" := e (in custom URValue at level 0, e ident,  only parsing).
Notation "e" := e (in custom ULValue at level 0, e ident,  only parsing).
Notation "% e" := (URScalar e) (in custom URValue at level 20, e bigint,  only parsing).
Notation "@ e" := (URScalar e) (in custom URValue at level 20, e global,  only parsing).
(* Notation "e" := e (in custom URValue at level 0, e global). *)
Tactic Notation "::" uconstr(s)  := (refine s).
Tactic Notation "?::" uconstr(s)  := (elpi refine_new (s)).
Notation " r '->' f " := (URField f r) (in custom URValue at level 2 , f global) : ursus_scope.
Notation " r '->' f " := (ULField f r) (in custom ULValue at level 2 , f global) : ursus_scope.


