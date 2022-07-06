Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Setoid. 
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Ascii.
Require Import String.

Require Import FinProof.Common.
Require Import FinProof.MonadTransformers21.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.

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

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Import UrsusNotations.
Local Open Scope xlist_scope.
Local Open Scope record.
Local Open Scope program_scope.
(* Local Open Scope glist_scope. *)
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.

From elpi Require Import elpi.

Local Open Scope string_scope.

Definition _static (T:Type): Type := T.
Definition _defqueue (M:Type -> Type) (I: Type) : Type := M I.
Definition _public (T:Type): Type := T.
Inductive  _ResolveName : string -> Type := _resolve_name : forall s, _ResolveName s.

Elpi Db string_utils lp:{{

pred starts_with  i:string, i:string.
starts_with S1 S2 :- 
  (K1 is size S1),
  (K2 is size S2),
  (K1 =< K2),
  (S21 is substring S2 0 K1),
  /* coq.say S21, */
  S1 = S21.

pred split_string  i:string, i:string, i:string, o:list string.
split_string Acc P S SL :-
    starts_with P S,
    (KS is size S),
    (KP is size P),
    (KS > KP), 
    /* coq.say S KS KP, */
    (SS is substring S KP (KS - KP)), !,
    /* coq.say SS, */
    split_string "" P SS SLL,
    (/* ((Acc = ""), (SL = SLL) ); */ SL = [Acc | SLL]). 
split_string Acc P S [Acc, ""] :-
    not(Acc = ""),
    starts_with P S,
    (KS is size S),
    (KP is size P),
    (KS = KP).
split_string Acc P S [""] :-
    (Acc = ""),
    starts_with P S,
    (KS is size S),
    (KP is size P),
    (KS = KP).
/* split_string Acc P S [] :-
    (Acc = ""),
    starts_with P S,
    (KS is size S),
    (KP is size P),
    (KS = KP). */
split_string Acc _P "" [Acc] .
/* split_string Acc P "" [] :-
  Acc = "". */
split_string Acc P S SL :-
  (K is size S),
  (A is substring S 0 1),
  (B is substring S 1 (K - 1)),
  (Acc1 is Acc ^ A),
  split_string Acc1 P B SL.

:index (_ 1)
pred join i:string, i:list string,  o:string.
join _ [] "".
join _ [X] X :- !.
join Sep [X|XS] S :- join Sep XS S0, S is X ^ Sep ^ S0.


pred char->term i:string, o:term.
char->term "A" {{ "A"%char }}:-!.
char->term "B" {{ "B"%char }}:-!.
char->term "C" {{ "C"%char }}:-!.
char->term "D" {{ "D"%char }}:-!.
char->term "E" {{ "E"%char }}:-!.
char->term "F" {{ "F"%char }}:-!.
char->term "G" {{ "G"%char }}:-!.
char->term "H" {{ "H"%char }}:-!.
char->term "I" {{ "I"%char }}:-!.
char->term "J" {{ "J"%char }}:-!.
char->term "K" {{ "K"%char }}:-!.
char->term "L" {{ "L"%char }}:-!.
char->term "M" {{ "M"%char }}:-!.
char->term "N" {{ "N"%char }}:-!.
char->term "O" {{ "O"%char }}:-!.
char->term "P" {{ "P"%char }}:-!.
char->term "Q" {{ "Q"%char }}:-!.
char->term "R" {{ "R"%char }}:-!.
char->term "S" {{ "S"%char }}:-!.
char->term "T" {{ "T"%char }}:-!.
char->term "U" {{ "U"%char }}:-!.
char->term "V" {{ "V"%char }}:-!.
char->term "W" {{ "W"%char }}:-!.
char->term "X" {{ "X"%char }}:-!.
char->term "Y" {{ "Y"%char }}:-!.
char->term "Z" {{ "Z"%char }}:-!.


char->term "a" {{ "a"%char }}:-!.
char->term "b" {{ "b"%char }}:-!.
char->term "c" {{ "c"%char }}:-!.
char->term "d" {{ "d"%char }}:-!.
char->term "e" {{ "e"%char }}:-!.
char->term "f" {{ "f"%char }}:-!.
char->term "g" {{ "g"%char }}:-!.
char->term "h" {{ "h"%char }}:-!.
char->term "i" {{ "i"%char }}:-!.
char->term "j" {{ "j"%char }}:-!.
char->term "k" {{ "k"%char }}:-!.
char->term "l" {{ "l"%char }}:-!.
char->term "m" {{ "m"%char }}:-!.
char->term "n" {{ "n"%char }}:-!.
char->term "o" {{ "o"%char }}:-!.
char->term "p" {{ "p"%char }}:-!.
char->term "q" {{ "q"%char }}:-!.
char->term "r" {{ "r"%char }}:-!.
char->term "s" {{ "s"%char }}:-!.
char->term "t" {{ "t"%char }}:-!.
char->term "u" {{ "u"%char }}:-!.
char->term "v" {{ "v"%char }}:-!.
char->term "w" {{ "w"%char }}:-!.
char->term "x" {{ "x"%char }}:-!.
char->term "y" {{ "y"%char }}:-!.
char->term "z" {{ "z"%char }}:-!.

char->term " " {{ " "%char }}:-!.
char->term "!" {{ "!"%char }}:-!.
char->term "@" {{ "@"%char }}:-!.
char->term "#" {{ "#"%char }}:-!.
char->term "%" {{ "%"%char }}:-!.
char->term "^" {{ "^"%char }}:-!.
char->term "&" {{ "&"%char }}:-!.
char->term "*" {{ "*"%char }}:-!.
char->term "(" {{ "("%char }}:-!.
char->term ")" {{ ")"%char }}:-!.
char->term "-" {{ "-"%char }}:-!.
char->term "_" {{ "_"%char }}:-!.
char->term "+" {{ "+"%char }}:-!.
char->term "{" {{ "{"%char }}:-!.
char->term "}" {{ "}"%char }}:-!.
char->term "\\" {{ "\"%char }}:-!.
char->term "/" {{ "/"%char }}:-!.
char->term "\n" {{ "
"%char }}:-!.
char->term "?" {{ "?"%char }}:-!.
char->term "," {{ ","%char }}:-!.
char->term "." {{ "."%char }}:-!.
char->term "[" {{ "["%char }}:-!.
char->term "]" {{ "]"%char }}:-!.

char->term "'" {{ "'"%char }}:-!.
char->term "`" {{ "`"%char }}:-!.
char->term "~" {{ "~"%char }}:-!.
char->term ">" {{ ">"%char }}:-!.
char->term "<" {{ "<"%char }}:-!.
char->term ":" {{ ":"%char }}:-!.
char->term ";" {{ ";"%char }}:-!.
char->term "=" {{ "="%char }}:-!.
char->term "$" {{ "$"%char }}:-!.
char->term "&" {{ "&"%char }}:-!.
char->term "|" {{ "|"%char }}:-!.

char->term "0" {{ "0"%char }}:-!.
char->term "1" {{ "1"%char }}:-!.
char->term "2" {{ "2"%char }}:-!.
char->term "3" {{ "3"%char }}:-!.
char->term "4" {{ "4"%char }}:-!.
char->term "5" {{ "5"%char }}:-!.
char->term "6" {{ "6"%char }}:-!.
char->term "7" {{ "7"%char }}:-!.
char->term "8" {{ "8"%char }}:-!.
char->term "9" {{ "9"%char }}:-!.

char->term _ _ :- coq.error "char not found".

pred string->term i:string, o:term.
string->term S T :- 
  (K is size S),
  (K = 1), !,
  char->term S C,
  (T = {{ String lp:C EmptyString}}).
string->term S T :- 
  (K is size S),
  (Pre is substring S 0 1),
  (Suf is substring S 1 (K - 1)),
  (char->term Pre PreT),
  (T = {{ String lp:PreT lp:RR}}),
  string->term Suf RR.

pred escape_all i:string, o:string.
escape_all ExprS ExprSEsc3 :-
  split_string "" "\n" ExprS SL,
  coq.say SL,
  join "\\\n" SL ExprSEsc1,

  split_string "" "/" ExprSEsc1 SL1,
  coq.say SL1,
  join "\\/" SL1 ExprSEsc2,
  
  split_string "" "&" ExprSEsc2 SL2,
  coq.say SL2,
  join "\\&" SL2 ExprSEsc3.

}}.


Elpi Db global_fields_utils lp:{{
pred fields->clist i:term, i:record-decl, o: list indc-decl.
fields->clist _ end-record [ ].
fields->clist T (field _ N _ NS) [ constructor XX (arity T) | M] :- XX is "_" ^ N, 
                                   fields->clist T (NS _) M.
fields->clist _ X _ :- coq.say "error",
                       coq.error X.

pred fields->lclist i:term, i:record-decl, o: list indc-decl.
fields->lclist _ end-record [ ].
fields->lclist T (field _ N _ NS) [ constructor XX (arity T) | M] :- XX is /* "_" ^ */ N, 
                                    fields->lclist T (NS _) M.
fields->lclist _ X _ :- coq.say "error",
                       coq.error X.                    

pred fields->tlist i:term, i:record-decl, o: term.
fields->tlist  _ end-record {{ [ ]%glist }}.
fields->tlist  T (field _ _ {{ _ResolveName lp:S}}  NS) {{ ((lp:A: Type)::lp:M)%glist  }} :- 
                                  coq.term->string S SS,
                                  (K is size SS),
                                  (SSS is substring SS 1 (K - 2)),
                                  SSN is SSS ^ "LRecord",
                                  get_name SSN A,
                                  fields->tlist T (NS _) M. 
fields->tlist  T (field _ _ A NS) {{ ((lp:A: Type)::lp:M)%glist  }} :-  
                                  fields->tlist T (NS _) M. 
fields->tlist  _ X _ :- coq.say "error",
                        coq.error X.

pred fields->ltlist i:term, i:record-decl, o: term.
fields->ltlist  _ end-record {{ [ ]%llist }}.
fields->ltlist  T (field _ _ {{ _ResolveName lp:S}}  NS) {{ ((lp:A: Type)::lp:M)%llist  }} :- 
                                  coq.term->string S SS,
                                  (K is size SS),
                                  (SSS is substring SS 1 (K - 2)),
                                  SSN is SSS ^ "LRecord",
                                  get_name SSN A,
                                  fields->ltlist T (NS _) M.
fields->ltlist  T (field _ _ A NS) {{ ((lp:A: Type)::lp:M)%llist  }} :-  
                                  fields->ltlist T (NS _) M. 
fields->ltlist  _ X _ :- coq.say "error",
                         coq.error X.                        

pred fields->sclist i:term, i:record-decl, o: list indc-decl.
fields->sclist  _ end-record [ ].
fields->sclist  T (field _ N {{_static _}} NS) [ constructor XX (arity T) | M] :- XX is "s_" ^ N, 
                                  fields->sclist T (NS _) M.
fields->sclist  T (field _ _ _ NS) M :- fields->sclist T (NS _) M. 
fields->sclist  _ X _ :- coq.say "error",
                         coq.error X.

pred fields->stlist i:term, i:record-decl, o: term.
fields->stlist  _ end-record {{ [ ]%llist }}.
fields->stlist  T (field _ _ {{_static lp:A}} NS) {{ ((lp:A: Type)::lp:M)%llist }} :-  
                                  fields->stlist T (NS _) M.
fields->stlist  T (field _ _ _ NS) M :- fields->stlist T (NS _) M.
fields->stlist  _ X _ :- coq.say "error",
                         coq.error X.

pred get_name i:string , o:term. 
 get_name NameS NameG :- 
 coq.locate NameS GR , 
 NameG = global GR .

}}.

Elpi Db generate_record_internals lp:{{

pred generate_record_internals i:id, i:record-decl, o:string, o:string, o:prop.
generate_record_internals N FDecl NF NTL _:-
    /* type record      id -> term -> id -> record-decl -> indt-decl. */
    NF is N ^ "Fields",
    @global! => coq.env.add-indt (inductive NF
                                  tt 
                                  (arity {{ Set }}) 
                                  (t\ {fields->clist t FDecl})) _,
    fields->tlist _ FDecl TL,
    std.assert-ok! (coq.elaborate-skeleton TL TY100 Body100) "Error" , 
    NTL is N ^ "L",
    @global! => coq.env.add-const NTL Body100 TY100 @transparent! _ 
    . 

pred local_generate_record_internals i:id, i:record-decl, o:string, o:string, o:prop.
local_generate_record_internals N FDecl NF NTL _:-
    /* type record      id -> term -> id -> record-decl -> indt-decl. */
    NF is N ^ "Fields",
    @global! => coq.env.add-indt (inductive NF
                                  tt 
                                  (arity {{ Set }}) 
                                  (t\ {fields->lclist t FDecl})) _,
    fields->ltlist _ FDecl TL,
    std.assert-ok! (coq.elaborate-skeleton TL TY100 Body100) "Error" , 
    NTL is N ^ "L",
    @global! => coq.env.add-const NTL Body100 TY100 @transparent! _ 
    . 
}}.

Elpi Command GlobalDeclareRecordInternals.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db generate_record_internals.
Elpi Accumulate Db global_generate_pruvendo_record.
 
Elpi Accumulate lp:{{ 
main [ indt-decl D ] :- 
    std.assert-ok! (coq.elaborate-indt-decl-skeleton D D1) "illtyped",
    D1 = record N _ _ FDecl,

    generate_record_internals N FDecl NF NTL _,
    global_generate_pruvendo_record NTL NF _. 
}}.

Elpi Typecheck.
Elpi Export GlobalDeclareRecordInternals.
 
Elpi Db declare_contract_internals lp:{{

pred generate_static_internals i:id, i:record-decl, o:string, o:string, o:prop.
generate_static_internals N FDecl NFS NTLS _:-
    NFS is N ^ "VarInitFields",
     @global! => coq.env.add-indt (inductive NFS
                                tt 
                                (arity {{ Set }})  /* Set !!! */
                                (t\ {fields->sclist t FDecl})) _,
    fields->stlist _ FDecl STL ,
    std.assert-ok! (coq.elaborate-skeleton STL TY200 Body200) "Error" , 
    NTLS is N ^ "VarInitL",
     @global! => coq.env.add-const NTLS Body200 TY200 @transparent! _
    .

pred make_field i:string, i:term, i:term, i:term, i:term, o:prop.
make_field N A ET UL UR _ :-
        NN is  "_" ^ N,
        get_name NN NT,  

        XL is N ^ "_left", 
        std.assert-ok! (coq.elaborate-skeleton 
        {{ 
            ULState Ledger_MainState (lp:ET lp:NT) : lp:UL lp:A 
        }} TY Body) "Error" , 

        coq.env.add-const XL Body TY @transparent! _, 

        XR is N ^ "_right", 
        std.assert-ok! (coq.elaborate-skeleton 
        {{
            URState Ledger_MainState (H:=lp:ET lp:NT) : lp:UR lp:A false 
        }} TY1 Body1) "Error" , 
        coq.env.add-const XR Body1 TY1 @transparent! _,
        /* Notation " 'counter' " := ( counter_left ) (in custom ULValue at level 0) : ursus_scope. */
        get_name XL XLGR,
        get_name XR XRGR,
        NLN is "'" ^ N ^ "'",
        @global! => coq.notation.add-notation NLN 
                    []
                    (some "ursus_scope") 
                    (some "ULValue")
                    (some 0)
                    XLGR 
                    ff _ ,
         @global! => coq.notation.add-notation NLN 
                    []
                    (some "ursus_scope") 
                    (some "URValue")
                    (some 0)
                    XRGR 
                    ff _ .

/* ( ULState Ledger_MainState (ContractLEmbeddedType _counter) : ULValue uint256) */
pred ursus_fields i:record-decl, i:term, i:term, i:term, o:prop.
ursus_fields end-record _ _ _ true.
ursus_fields (field _ N {{ _ResolveName lp:S}} NS) ET UL UR R:-
                                  coq.term->string S SS,
                                  (K is size SS),
                                  (SSS is substring SS 1 (K - 2)),
                                  SSN is SSS ^ "LRecord",
                                  get_name SSN A,
                                  make_field N A ET UL UR _,
                                  ursus_fields (NS _) ET UL UR R.
ursus_fields (field _ N A NS) ET UL UR R :- 
                                  make_field N A ET UL UR _,
                                  ursus_fields (NS _) ET UL UR R.
ursus_fields X _ _ _ false :- coq.say "error",
                              coq.error X.

pred declare_contract_internals i:argument.
declare_contract_internals (indt-decl D) :- 
    std.assert-ok! (coq.elaborate-indt-decl-skeleton D D1) "illtyped",
    D1 = record NN _ _ FDecl,

    generate_record_internals NN  FDecl NF NTL _ ,
    generate_static_internals NN  FDecl NFS NTLS _ ,

    global_generate_pruvendo_record NTL NF _  ,
    local_generate_pruvendo_record NTLS NFS _ ,

    LS is "LedgerL",
    CTLR is NTL ^ "Record",

    get_name CTLR CT,
    get_name "MessagesAndEventsLRecord"  MT,
    get_name "VMStateLRecord"  VT,
    get_name "LocalStateLRecord"  LT,

    std.assert-ok! (coq.elaborate-skeleton {{ [ lp:CT : Type ; 
                                                lp:CT : Type ; 
                                                lp:MT : Type ; 
                                                lp:MT : Type ; 
                                                lp:VT : Type ; 
                                                lp:LT : Type ; 
                                                lp:LT : Type ]%glist }} TY1 Body1) "Error", 
    coq.env.add-const LS Body1 TY1 @transparent! _ , 
    coq.say LS " is added",
    /* get_name LS LGR, */
    global_generate_pruvendo_record LS "LedgerFields" _  ,
    LPRS is LS ^ "PruvendoRecord",
    get_name LPRS LPR,
    LETS is LS ^ "EmbeddedType",
    get_name LETS LET,
    get_name "LocalDefault" LD,
    get_name "MessagesAndEventsLEmbeddedType" MET,
    LRS is LS ^ "Record",
    get_name LRS LR, 
    get_name "_GlobalParams" GP,
    get_name "_OutgoingMessageParams" OMP,
    
    LLCS is LS ^ "LedgerClass", 
    std.assert-ok! (coq.elaborate-skeleton {{ 
      Build_LedgerClass lp:CT 
                        lp:LPR 
                        lp:LET
                        lp:LD
                        eq_refl
                        eq_refl
                        ( VMStateLEmbeddedType VMState_ι_isCommitted )
                        eq_refl
                        eq_refl
                        eq_refl
                        eq_refl
                        ( lp:MET lp:GP )
                        ( lp:MET lp:OMP )
                        (simpleStateMonadState lp:LR) : LedgerClass XBool lp:LR lp:CT 
                                        lp:LT VMStateLRecord lp:MT 
                                        GlobalParamsLRecord OutgoingMessageParamsLRecord
     }} TY2 Body2) "Error" , 
    coq.env.add-const LLCS Body2 TY2 @transparent! _ , 
    coq.locate LLCS LLC, 
    get_name LLCS LLCGR, 
    @global! => coq.TC.declare-instance LLC 0,
    /* @UExpressionL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass */
    std.assert-ok! (coq.elaborate-skeleton {{ @UExpressionL 
                                                      lp:LR 
                                                      lp:CT 
                                                      lp:LT 
                                                      lp:VT 
                                                      lp:MT 
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR }} TY3 Body3) "Error" , 
    @global! => coq.env.add-const "public" Body3 TY3 @transparent! _ ,       
    @global! => coq.env.add-const "private" Body3 TY3 @transparent! _ ,   
    @global! => coq.env.add-const "external" Body3 TY3 @transparent! _ ,   
    @global! => coq.env.add-const "internal" Body3 TY3 @transparent! _ ,                                                      
    /* coq.notation.add-abbreviation "public" 0 Body3 ff _,
    coq.notation.add-abbreviation "private" 0 Body3 ff _, */
    @global! => coq.notation.add-notation "'UExpression'"
                    []
                    (some "ursus_scope") 
                    (none)
                    (some 0)
                    Body3 
                    ff _,
    /* @ULValueL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass */
    std.assert-ok! (coq.elaborate-skeleton {{  @ULValueL 
                                                      lp:LR 
                                                      lp:CT 
                                                      lp:LT 
                                                      lp:VT 
                                                      lp:MT 
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR }} _ Body4) "Error" , 
    /* @global! => coq.env.add-const "ULValue" Body4 TY4 @transparent! _ ,  */
    @global! => coq.notation.add-abbreviation "ULValue" 0 Body4 ff _,
   /*  @global! => coq.notation.add-notation "'ULValue'"
                    []
                    (some "ursus_scope") 
                    (none)
                    (some 0)
                    Body4 
                    ff _, */
    /* @URValueL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass */
    std.assert-ok! (coq.elaborate-skeleton {{  @URValueL 
                                                      lp:LR 
                                                      lp:CT 
                                                      lp:LT 
                                                      lp:VT 
                                                      lp:MT 
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR }} _TY5 Body5) "Error" , 
    coq.notation.add-abbreviation "URValue" 0 Body5 ff _,
    /* @global! => coq.notation.add-notation "'URValue'"
                    []
                    (some "ursus_scope") 
                    (none)
                    (some 0)
                    Body5 
                    ff _, */
    /*  (@wrapULExpressionL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass _ _ _ _ ) */
    std.assert-ok! (coq.elaborate-skeleton {{ fun x => fun y => fun z => fun t => fun u =>
                                              @wrapULExpressionL 
                                                      lp:LR 
                                                      lp:CT 
                                                      lp:LT 
                                                      lp:VT 
                                                      lp:MT 
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR x y z t u }} _ Body6) "Error" , 
    /* coq.notation.add-abbreviation "wrapULExpression" 5 Body6 ff _, */
    /* (R X)%type_scope b%bool_scope H u */
    @global! => coq.notation.add-notation "'wrapULExpression' R X b H u"
                    [pr "R" (pr none (some 0)),  pr "X" (pr none (some 0)), pr "b" (pr none (some 0)), pr "H" (pr none (some 0)), pr "u" (pr none (some 0))]
                    (some "ursus_scope") 
                    (none)
                    (some 0)
                    Body6 
                    ff _,
    /*  (@ursus_call_with_argsL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass _ _  ) */
    std.assert-ok! (coq.elaborate-skeleton {{ fun x => fun y => fun z =>
                                              @ursus_call_with_argsL 
                                                      lp:LR 
                                                      lp:CT 
                                                      lp:LT 
                                                      lp:VT 
                                                      lp:MT 
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR x y z }} _ Body7) "Error" , 
    /* coq.notation.add-abbreviation "ursus_call_with_args" 3 Body7 ff _, */
    /* b%bool_scope T%type_scope LedgerableWithArgs */
    @global! => coq.notation.add-notation "'ursus_call_with_args' b T L"
                    [pr "b" (pr none (some 0)),  pr "T" (pr none (some 0)), pr "L" (pr none (some 0))]
                    (some "ursus_scope") 
                    (none)
                    (some 0)
                    Body7 
                    ff _,
    /* (@wrapURExpressionL LedgerLRecord ContractLRecord LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord GlobalParamsLRecord OutgoingMessageParamsLRecord ledgerClass _ _ _ ) */
    std.assert-ok! (coq.elaborate-skeleton {{ fun x => fun y => fun z => fun t =>
                                              @wrapURExpressionL 
                                                      lp:LR 
                                                      lp:CT 
                                                      lp:LT 
                                                      lp:VT 
                                                      lp:MT 
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR x y z t }} _ Body8) "Error" , 
    /* coq.notation.add-abbreviation "wrapURExpression" 4 Body8 ff _, */
    /* X%type_scope b%bool_scope H u */
    @global! => coq.notation.add-notation "'wrapURExpression' X b H u"
                    [pr "X" (pr none (some 0)),  pr "b" (pr none (some 0)), pr "H" (pr none (some 0)),  pr "u" (pr none (some 0))]
                    (some "ursus_scope") 
                    (none)
                    (some 0)
                    Body8
                    ff _,
    /* Notation DefaultMessageQueue := 
                 (@DefaultMessageQueue LedgerLRecord ContractLRecord LocalStateLRecord MessagesAndEventsLRecord ledgerClass). */
    std.assert-ok! (coq.elaborate-skeleton {{ @DefaultMessageQueue 
                                                      lp:LR 
                                                      lp:CT 
                                                      lp:LT
                                                      lp:MT  
                                                      lp:LLCGR }} _ Body9) "Error" , 
    /* coq.notation.add-abbreviation "DefaultMessageQueue" 0 Body9 ff _, */
    @global! => coq.notation.add-notation "'DefaultMessageQueue'"
                    []
                    (some "ursus_scope") 
                    (none)
                    (some 0)
                    Body9 
                    ff _,
    /* Notation LocalStateField' := (LocalStateField XHMap LocalStateLRecord). */
    std.assert-ok! (coq.elaborate-skeleton {{ LocalStateField mapping lp:LT }} _ Body10) "Error" , 
    /* coq.notation.add-abbreviation "LocalStateField'" 0 Body10 ff _, */
    @global! => coq.notation.add-notation "'LocalStateField''"
                    []
                    (some "ursus_scope") 
                    (none)
                    (some 0)
                    Body10 
                    ff _,
    CETS is NTL ^ "EmbeddedType" ,
    get_name CETS CET,
    /* coq.notation.abbreviation-body ULV 1 ULVT  , */
    /* coq.notation.abbreviation-body URV 2 URVT  , */
    /* Definition modifier := forall X b, UExpression X b -> UExpression X true .
       Tactic Notation "unfold_mod" := (unfold modifier; intros X b u). */
    std.assert-ok! (coq.elaborate-skeleton {{ forall X b, lp:Body3 X b -> lp:Body3 X true }} TY11 Body11) "Error" ,   
    @global! => coq.env.add-const "modifier" Body11 TY11 @transparent! _ ,       
    ursus_fields FDecl CET Body4 Body5 _ .
}}.

Elpi Command GlobalDeclareContractInternals.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db generate_record_internals.
Elpi Accumulate Db local_generate_pruvendo_record.
Elpi Accumulate Db global_generate_pruvendo_record.
Elpi Accumulate Db declare_contract_internals.

Elpi Accumulate lp:{{

main [ indt-decl D ] :-
 declare_contract_internals (indt-decl D).

}}.

Elpi Typecheck.

Elpi Export GlobalDeclareContractInternals.


Elpi Command MakeUrsusDefinitions.
  
Elpi Accumulate Db global_fields_utils.

Elpi Accumulate lp:{{ 

pred num_args i:term , o:int.
num_args (prod _ _ F) K :- num_args ( F _ ) M, K = M + 1.
num_args _ 0.

pred make_arg_str i:term , i: string,  o:string.
make_arg_str (prod X _ F) "" Newacc :-  !, coq.name->id X N, 
                                        Nacc = " " ^ N ,                      
                                        make_arg_str ( F _ )  Nacc Newacc.
make_arg_str (prod X _ F) Acc Newacc :- !, coq.name->id X N,
                                        Nacc = Acc ^ " , " ^ N,                               
                                        make_arg_str ( F _ )  Nacc Newacc.
make_arg_str _ "" Newacc :- !, Newacc is "( )".
make_arg_str _ Acc Newacc :- !, Newacc is "(" ^ Acc ^ " )".
make_arg_str T In _ :- coq.error "error in make_arg_str: " T "->" In.

pred add_tail i:list X, i:X, o:list X.
add_tail [] X [X] :- !.
add_tail [H|T] X [H|TT] :- !, add_tail T X TT.

pred lrepeat i:X , i:int , o:list X.
lrepeat _ 0 [] :- !.
lrepeat A K [A|T] :- !, K1 = K - 1, lrepeat A K1 T.
lrepeat _ _ _ :- coq.error "error".

pred app_left_lambdas i:term , i:term, i:term , i:term, i:term , i:term, i:list((term -> term) -> term), i:list term, i:term, o:term.
app_left_lambdas LR CT LT VT MT LLCGR [fun A AT | TL] X T R :- R = /* fun `M` {{Type}} M\ */ fun A AT a\ {app_left_lambdas LR CT LT VT MT LLCGR TL {add_tail X a} T}.
app_left_lambdas LR CT LT VT MT LLCGR [] X (app [_|Args]) R :- 
                      std.rev Args [B|_],
                      R =  fun `T` _ T\ 
                      {{ @wrapULExpressionL lp:LR 
                                            lp:CT 
                                            lp:LT 
                                            lp:VT 
                                            lp:MT 
                                            GlobalParamsLRecord 
                                            OutgoingMessageParamsLRecord 
                                            lp:LLCGR lp:T _ _ _ lp:{{app X}}: @UExpressionL 
                                                                            lp:LR 
                                                                            lp:CT 
                                                                            lp:LT 
                                                                            lp:VT 
                                                                            lp:MT 
                                                                            GlobalParamsLRecord 
                                                                            OutgoingMessageParamsLRecord 
                                                                            lp:LLCGR lp:T lp:B }}.                      

pred app_right_lambdas i:term , i:term, i:term , i:term, i:term , i:term, i:list((term -> term) -> term), i:list term, i:term, o:term.
app_right_lambdas LR CT LT VT MT LLCGR [fun A AT | TL] X T R :- R = fun A AT a\ {app_right_lambdas LR CT LT VT MT LLCGR TL {add_tail X a} T}.
app_right_lambdas LR CT LT VT MT LLCGR [] X (app [_|Args]) R :- 
                std.rev Args [B,F|_],
                R  =  {{@wrapURExpressionL  lp:LR 
                                            lp:CT 
                                            lp:LT 
                                            lp:VT 
                                            lp:MT 
                                            GlobalParamsLRecord 
                                            OutgoingMessageParamsLRecord 
                                            lp:LLCGR _ _ _ lp:{{app X}}: @URValueL  lp:LR 
                                                                                  lp:CT 
                                                                                  lp:LT 
                                                                                  lp:VT 
                                                                                  lp:MT 
                                                                                  GlobalParamsLRecord 
                                                                                  OutgoingMessageParamsLRecord 
                                                                                  lp:LLCGR lp:F lp:B}}.                                            

pred mk_lambdas i:term , i:term, i:term , i:term, i:term , i:term, 
                i:term, 
                o:list((term -> term) -> term), 
                o:term, 
                o:list implicit_kind, 
                o:list (pair id (pair (option id) (option int))),
                o:term.
mk_lambdas LR CT LT VT MT LLCGR (prod A {{@ULValueL lp:LR lp:CT lp:LT lp:VT lp:MT GlobalParamsLRecord OutgoingMessageParamsLRecord lp:LLCGR lp:AT}} F) R L [explicit|Imps] [(pr AS (pr (some "ULValue") (some 0)))|Args] T:-
                              coq.name->id A AS, 
                              (R = [fun A {{@ULValueL lp:LR lp:CT lp:LT lp:VT lp:MT GlobalParamsLRecord OutgoingMessageParamsLRecord lp:LLCGR lp:AT}} | R1]),
                              (L = {{@UExpressionP_Next_LedgerableWithLArgsL _ _ _ _ _ _ _ _ _ _ _ lp:L1}}),
                              mk_lambdas LR CT LT VT MT LLCGR (F _) R1 L1 Imps Args T.
mk_lambdas LR CT LT VT MT LLCGR (prod A AT F) R L [explicit|Imps] [(pr AS (pr (some "URValue") (some 0)))|Args] T :- 
                              coq.name->id A AS,
                              (R = [fun A {{@URValueL lp:LR lp:CT lp:LT lp:VT lp:MT GlobalParamsLRecord OutgoingMessageParamsLRecord lp:LLCGR lp:AT false}} | R1]),
                              (L = {{@UExpressionP_Next_LedgerableWithRArgsL _ _ _ _ _ _ _ _ _ _ _ _ lp:L1}}),
                              mk_lambdas LR CT LT VT MT LLCGR (F _) R1 L1 Imps Args T.
mk_lambdas _ _ _ _ _ _ T [] {{λ0}} [] [] T.  

pred mk_notation_term i:list((term -> term) -> term), i:term, o:term.
mk_notation_term [fun A AT | TL] Trm R :- 
   R = fun A AT a\ {mk_notation_term TL {{lp:Trm lp:a}} }.
mk_notation_term [] Trm Trm.  

pred mk_left_ursus i:term , i:term, i:term , i:term, i:term , i:term, 
                   i:list((term -> term) -> term),
                   i:term,
                   i:term,
                   i:string,
                   i:list implicit_kind,
                   i:list (pair id (pair (option id) (option int))),
                   i:term,
                   i:string,
                   o:prop.
mk_left_ursus LR CT LTT VT MT LLCGR   LT Lam AGR A Imps Args T AS _ :- 
    app_left_lambdas LR CT LTT VT MT LLCGR  LT [ {{@ursus_call_with_argsL lp:LR 
                                                      lp:CT 
                                                      lp:LTT 
                                                      lp:VT 
                                                      lp:MT 
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR _ _ lp:Lam}} , AGR ] T UC,
    std.assert-ok! (coq.elaborate-skeleton UC TY Body) "Error" ,
    AL is A ^ "_left",
    @global! => coq.env.add-const AL Body TY @transparent! _ ,
    coq.locate AL ALGR,
    add_tail Imps maximal Impss ,
    coq.arguments.set-implicit ALGR [ Impss ] ,
    NL is "'" ^ A ^ "' " ^ AS,
    ALT = global ALGR,
    mk_notation_term LT ALT ALT1,
    @global! => coq.notation.add-notation NL 
                    Args
                    (some "ursus_scope") 
                    (some "ULValue")
                    (some 0)
                    ALT1 
                    ff _.

pred mk_right_ursus i:term , i:term, i:term , i:term, i:term , i:term, 
                    i:list((term -> term) -> term),
                    i:term,
                    i:term,
                    i:string,
                    i:list implicit_kind,
                    i:list (pair id (pair (option id) (option int))),
                    i:term,
                    i:string,
                    o:prop.
mk_right_ursus LR CT LTT VT MT LLCGR  LT Lam AGR A _ Args T AS _ :- 
    app_right_lambdas LR CT LTT VT MT LLCGR    LT [ {{@ursus_call_with_argsL lp:LR 
                                                      lp:CT 
                                                      lp:LTT 
                                                      lp:VT 
                                                      lp:MT 
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR _ _ lp:Lam}} , AGR ] T UC,
    std.assert-ok! (coq.elaborate-skeleton UC TY Body) "Error" ,
    AR is A ^ "_right",
    @global! => coq.env.add-const AR Body TY @transparent! _ ,
    coq.locate AR ARGR,
    NR is "'" ^ A ^ "' " ^ AS,
    ART = global ARGR,
    mk_notation_term LT ART ART1,
    @global! => coq.notation.add-notation NR
                    Args
                    (some "ursus_scope") 
                    (some "URValue")
                    (some 0)
                    ART1 
                    ff _.

main [ str A ] :- 
    coq.say "Making Ursus call conventions...",
    get_name A AGR,
    coq.typecheck AGR Ty _,
   /*  coq.say Ty, */
    make_arg_str Ty "" AS,
   /*  coq.say "soo", */

    get_name "ContractLRecord" CT,
    get_name "LedgerLRecord"  LR,
    get_name "MessagesAndEventsLRecord"  MT,
    get_name "VMStateLRecord"  VT,
    get_name "LocalStateLRecord"  LTT,
    get_name "LedgerLLedgerClass" LLCGR,

    mk_lambdas     LR CT LTT VT MT LLCGR    Ty LT Lam Imps Args T  ,
    mk_left_ursus  LR CT LTT VT MT LLCGR    LT Lam AGR A Imps Args T AS _ ,
    mk_right_ursus LR CT LTT VT MT LLCGR    LT Lam AGR A Imps Args T AS _ ,
    
    coq.say "finished". 
}}.

Elpi Typecheck. 

Elpi Db make_message_queue lp:{{ 

pred mlist->tlist i:term, o: list term, o:term.
mlist->tlist {{ [ ]%glist }} [ ] _.
mlist->tlist {{ (lp:H::lp:XS)%glist }} [ X | M] D :- (H = let _ _ {{messageQueue lp:X}} _),
                                                    mlist->tlist XS M D.
mlist->tlist {{ (lp:H::lp:XS)%glist }} [ X | M] X :- (H = let _ _ {{_defqueue messageQueue lp:X}} _),
                                                    mlist->tlist XS M X.                                                    
mlist->tlist {{ (lp:H::lp:XS)%glist }} M D :- (H = let _ _ _ _),
                                              mlist->tlist XS M D.                                                    
mlist->tlist X _ _ :- coq.say "error",
                     coq.error X.

pred mk_lambdas i:term , i:term, i:term , i:term, i:term , i:term,
                i:int  , i:term, o:list((term -> term) -> term).
mk_lambdas LR CT LTT VT MT LLCGR    K (prod _ AT F) R :- term_to_string K KS, /* coq.say KS,  */
                              AS is "arg" ^ KS,
                              BS is "b" ^ KS, 
                              (R = [f \ fun {coq.id->name BS} {{bool}} b \
                                    fun {coq.id->name AS} {{@URValueL 
                                                            lp:LR 
                                                            lp:CT 
                                                            lp:LTT 
                                                            lp:VT 
                                                            lp:MT 
                                                            GlobalParamsLRecord 
                                                            OutgoingMessageParamsLRecord 
                                                            lp:LLCGR lp:AT lp:b }} f | R1]),
                               KN is (K + 1),
                               mk_lambdas LR CT LTT VT MT LLCGR KN (F _) R1.
mk_lambdas _ _ _ _ _ _    _ _ [].

pred add_tail i:list X, i:X, o:list X.
add_tail [] X [X] :- !.
add_tail [H|T] X [H|TT] :- !, add_tail T X TT.

pred length i:list A, o:int.
length [_|L] N :- length L N1, N is N1 + 1.
length []    0.

/* pred mk_ind_bind i:term, i:term, i:term , i:term, i:term , i:term, i:term , i:term,
                 i:list((term -> term) -> term) , i:term, i:term, i:term, i:list term , o:term.
mk_ind_bind II B LR CT LTT VT MT LLCGR [] A AT T Args R :- coq.say "tock...",
            (R = {{ @urvalue_bindL lp:LR lp:CT lp:LTT lp:VT lp:MT GlobalParamsLRecord OutgoingMessageParamsLRecord lp:LLCGR lp:AT lp:II lp:B _ lp:A lp:F }}),
            (F = fun _ AT a \ {coq.mk-app T [ a | Args] }).
mk_ind_bind II B LR CT LTT VT MT LLCGR [L | LXS] A AT T Args R :- coq.say "tick...",
                                (L _ = fun BS BT x \ fun AS (ATT x) _ ),
                                (ATT = x \ {{@URValueL _ _ _ _ _ _ _ _ lp:AA lp:x }}),
                                (R = fun _ AA x \ {mk_ind_bind II B LR CT LTT VT MT LLCGR LXS A AT T {add_tail Args x} } ).
 */

pred mk_term_right i:term, i:term, i:term , i:term, i:term , i:term, i:term , i:term, 
                   i:term, i:list((term -> term) -> term), i:list term, 
                   o:list implicit_kind,
                   o:list (pair id (pair (option id) (option int))),
                   o:term.
mk_term_right II Ro LR CT LTT VT MT LLCGR  I [ L | LXS ] F [maximal|[explicit|Imps]] Args1 R :-
              (L _ = fun BS BT x \ fun AS (AT x) _ ),
              (Args1 = [pr "" (pr none none) | [pr {coq.name->id AS} (pr (some "URValue") (some 0))|Args]]),
              (Ro1 = {{@URValueP_Next_URValueDWithArgsL _ _ _ _ _ _ _ _ _ _ _ _ lp:Ro}}),
              (R = fun BS BT b \ fun AS (AT b) a\ 
                  {mk_term_right II Ro1 LR CT LTT VT MT LLCGR I LXS {add_tail F a} Imps Args }).
mk_term_right II Ro LR CT LTT VT MT LLCGR  I [] F [] [] R :- (R = {{ lp:Rr : @URValueL 
                                                                    lp:LR 
                                                                    lp:CT 
                                                                    lp:LTT 
                                                                    lp:VT 
                                                                    lp:MT 
                                                                    GlobalParamsLRecord 
                                                                    OutgoingMessageParamsLRecord 
                                                                    lp:LLCGR lp:II _ }}),                                                                      
      (Rr = {coq.mk-app  {{URResult}} [ app [ {{ rvalued_call_with_argsL 
                      lp:LR lp:CT lp:LTT lp:VT lp:MT
                      GlobalParamsLRecord
                      OutgoingMessageParamsLRecord
                      lp:LLCGR _ _ lp:Ro}} | [ I | F ] ] ] } ).                   

pred rev i:list A, o:list A.
rev L RL  :- rev.aux L []  RL.
rev.aux [X|XS] ACC R :- rev.aux XS [X|ACC] R.
rev.aux [] L L.

pred rev_args i: term, i:list term, i:list((term -> term) -> term), o:term.
rev_args G AA [L|LXS] R :- 
              (L _ = fun _ _ x \ fun _ (AT x) _ ),
              (AT = x \ {{@URValueL _ _ _ _ _ _ _ _ lp:A lp:x }}),
              R = fun _ A x \ { rev_args G [x|AA] LXS }.
rev_args G AA [] (app [G | AA]) .

pred wrap_term i:term, i:term, i:list term, i:list((term -> term) -> term), o:term.
wrap_term W F AA [L|LXS] R :- (L _ = fun _ _ x \ fun _ (AT x) _ ),
                          (AT = x \ {{@URValueL _ _ _ _ _ _ _ _ lp:A lp:x }}),
                          R =  fun _ A x \ {wrap_term W F {add_tail AA x} LXS}.
wrap_term W F AA [] (app [W , app [F | AA] ]).

pred mk_notation_term i:list((term -> term) -> term), i:term, o:term.
mk_notation_term [L | TL] Trm R :- 
   (L _ = fun _ BT x \ fun AS (AT x) _ ),
   /* (AT = x \ {{@URValueL _ _ _ _ _ _ _ _ _ lp:x }}), */
   R = fun _ BT b \ fun AS (AT b) a\ {mk_notation_term TL {{lp:Trm lp:b lp:a}} }.
mk_notation_term [] Trm Trm. 

pred make_arg_str i:term , i: string, i:int,  o:string.
make_arg_str (prod _ _ F) "" K Newacc :-
                                        term_to_string K KS, 
                                        AS is "arg" ^ KS,
                                       /*  BS is "b" ^ KS,  */
                                        Nacc = " " ^ AS ,
                                        K1 is (K + 1),                      
                                        make_arg_str ( F _ )  Nacc K1 Newacc.
make_arg_str (prod _ _ F) Acc K Newacc :- term_to_string K KS, 
                                        AS is "arg" ^ KS,
                                       /*  BS is "b" ^ KS, */
                                        Nacc = Acc ^ " , " ^ AS, 
                                        K1 is (K + 1),                                        
                                        make_arg_str ( F _ )  Nacc K1 Newacc.
make_arg_str _ "" _ Newacc :- Newacc is "( )".
make_arg_str _ Acc _ Newacc :- Newacc is "(" ^ Acc ^ " )".
make_arg_str _ _ _ _ :- coq.error "error".

pred remove_prefix_underscore i:string, o:string.
remove_prefix_underscore S SS :- (K  is size S),
                                 (P is substring S 0 1),
                                 (P = "_"),
                                 (SS is substring S 1 (K - 1)).
remove_prefix_underscore S S.

pred mk_message_queue_instance_term i:term, i:list((term -> term) -> term), 
                                    i:list term, i:term, o:term, o:term.   
mk_message_queue_instance_term Int [L|LXS] FArgs F RF RT :-
                                (L _ = fun BS BT x \ fun AS (AT x) _ ),
                                (RF = fun BS BT x \ fun AS (AT x) y \ RF1),
                                (RT = prod BS BT b \ prod AS (AT b) a\ 
                                      {mk_message_queue_instance_term Int LXS {add_tail {add_tail FArgs b} a} F RF1 } ).
mk_message_queue_instance_term Int [] FArgs F F RT:-
                  (R = app FArgs),     
                  (RT = {{ MessageQueue lp:Int _ lp:R }}).                                                                      
                                                      

pred mk_int_right i:term , i:term, i:term , i:term, i:term , i:term,
                  i:id, i:list constructor, i:list term, o:prop.
mk_int_right LR CTT LTT VT MT LLCGR    IS [C|CXS] [CT|CXTS] R :- 
                                       coq.gref->id(indc C) CS,
                                       get_name CS CTrm,
                                       remove_prefix_underscore CS CSS,
                                       N is IS ^ "_" ^ CSS ^ "_right",
                                       get_name IS Int, 
                                       coq.say N , 
                                       mk_lambdas LR CTT LTT VT MT LLCGR   0 CT CTL,
                                       wrap_term {{@sInjectL lp:LR lp:CTT lp:LTT lp:VT lp:MT GlobalParamsLRecord 
                                                   OutgoingMessageParamsLRecord lp:LLCGR lp:Int}} CTrm [] CTL URT,
                                       mk_term_right Int {{ URValueP0_RValuedWithArgsL lp:LR lp:CTT lp:LTT lp:VT lp:MT
                                                              GlobalParamsLRecord
                                                              OutgoingMessageParamsLRecord
                                                              lp:LLCGR _ _ }} LR CTT LTT VT MT LLCGR    URT CTL [] Imps Args CR,
                                       coq.say Imps Args,                           
                                       
                                       std.assert-ok! (coq.elaborate-skeleton CR TY1 Body1) "Error" ,
                                       coq.say TY1,
                                       @global! => coq.env.add-const N Body1 TY1 @transparent! _,
                                       make_arg_str CT "" 0 ArgS,
                                       NR is "'" ^ IS ^ "." ^ CSS ^ "' " ^ ArgS,
                                       coq.locate N NGR,
                                       coq.arguments.set-implicit NGR [ Imps ] ,
                                       NTrm = global NGR,
                                       @global! => coq.notation.add-term-notation NR
                                                                             Args
                                                                             (some "ursus_scope") 
                                                                             (some "URValue")
                                                                             (some 0)
                                                                             NTrm 
                                                                             ff _,
                                       mk_message_queue_instance_term Int CTL [NTrm] F RF MQITT,
                                       NL is IS ^ "_left",
                                       get_name NL NLT,
                                       (F = {{ Build_MessageQueue _ _ _ lp:NLT }}) , 
                                       (MQ = {{ lp:RF:lp:MQITT }} ), 
                                       std.assert-ok! (coq.elaborate-skeleton MQ TY Body) "Error" , 
                                       MQN is  IS ^ "_" ^ CSS ^ "MQ",
                                       coq.env.add-const MQN Body TY @transparent! _ ,
                                       coq.locate MQN MQNGR , 
                                       @global! => coq.TC.declare-instance MQNGR 0,                                                                  
                                       mk_int_right LR CTT LTT VT MT LLCGR   IS CXS CXTS R.
mk_int_right _ _ _ _ _ _    _ [] [] true .                                      
mk_int_right _ _ _ _ _ _    _ _ _ false :- coq.error "Error in mk_int_right".


pred mk_interface_notations i:term , i:term, i:term , i:term, i:term , i:term,
                            i:term, o:prop.
mk_interface_notations LR CT LTT VT MT LLCGR  I _ :- coq.term->string I IS, 
                              coq.term->gref I (indt II),
                              coq.env.indt II _ _ _ _ LC LCT,
                              /* coq.say LC LCT, */
                              mk_int_right LR CT LTT VT MT LLCGR    IS LC LCT _ .


pred mk_lmessages i:term , i:term, i:term , i:term, i:term , i:term, i:term,
                  i:list constructor, i:list term, o:prop.
mk_lmessages LR CT LT VT MT LLCGR MET [C|CXS] [I|IXS] R :- coq.term->string I IS,
                          coq.gref->id (indc C) CS,
                          get_name CS CTrm,
                          L = {{ ULState Ledger_MessagesState 
                                         (lp:MET lp:CTrm):
                                 @ULValueL lp:LR 
                                          lp:CT 
                                          lp:LT 
                                          lp:VT 
                                          lp:MT 
                                          GlobalParamsLRecord 
                                          OutgoingMessageParamsLRecord 
                                          lp:LLCGR
                                          (messageQueue lp:I) }},
                          std.assert-ok! (coq.elaborate-skeleton L TY Body) "Error" ,
                          N is IS ^ "_left",  
                          @global! => coq.env.add-const N Body TY @transparent! _,
                          NN is "'" ^ IS ^ "Ptr'",
                          get_name N NNTrm,
                          @global! => coq.notation.add-term-notation NN
                                                                     []
                                                                     (some "ursus_scope") 
                                                                     (some "ULValue")
                                                                     (some 0)
                                                                     NNTrm 
                                                                     ff _,
                          mk_interface_notations LR CT LT VT MT LLCGR    I _,
                          mk_lmessages LR CT LT VT MT LLCGR MET CXS IXS R.
mk_lmessages _ _ _ _ _ _ _   _ _ _.                                  
                            

pred make_message_queue.
make_message_queue :- 
   coq.locate "MessagesAndEventsL"  MT,
   coq.locate "MessagesAndEventsFields"   MF,
   
   get_name "ContractLRecord" CT,
   get_name "LedgerLRecord"  LR,
   get_name "MessagesAndEventsLRecord"  MTT,
   get_name "VMStateLRecord"  VT,
   get_name "LocalStateLRecord"  LT,
   get_name "LedgerLLedgerClass" LLCGR,
   get_name "MessagesAndEventsLEmbeddedType" MET, 

   MF = indt MFI,
   MT = const MTC,
   coq.env.indt MFI _ _ _ _ LC _,
   /* coq.say LC, */
   coq.env.const MTC (some MTB) _,
   mlist->tlist MTB MTL DefM,
  /*  coq.say MTL, */
   mk_lmessages LR CT LT VT MTT LLCGR MET LC MTL _,
   DefIS is "_defaultMessageQueue",
   coq.term->string DefM DS,
   DLS is DS ^ "_left",
   get_name DLS DLT,
   std.assert-ok! (coq.elaborate-skeleton {{ 
                    Build_DefaultMessageQueue (lp:DLT:@ULValueL lp:LR 
                                                      lp:CT 
                                                      lp:LT 
                                                      lp:VT 
                                                      lp:MTT
                                                      GlobalParamsLRecord 
                                                      OutgoingMessageParamsLRecord 
                                                      lp:LLCGR (messageQueue lp:DefM)) }} TY Body) "Error" , 
   coq.env.add-const DefIS Body TY @transparent! _ ,
   coq.locate DefIS DefIGR , 
   @global! => coq.TC.declare-instance DefIGR 0.
}}.

About sInjectL.


Elpi Command MakeMessageQueues.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db make_message_queue.

Elpi Accumulate lp:{{

main [ ] :- make_message_queue.

}}.

Elpi Typecheck.
Elpi Export MakeMessageQueues.


(* Elpi Command Contract.

Elpi Accumulate Db global_fields_utils.

Elpi Accumulate lp:{{ 

main [ str A ] :- 
  SN is A ^ "Section",
  coq.env.begin-section SN,
  coq.env.add-section-variable "LocalStateLRecord" {{ Type (* @{XDefault.u0} *) }} LC,
  LCT = global (const LC),
  LD = {{XDefault lp:LCT}},
  coq.typecheck LD _ _, /* to avoid universes information incompleteness */
  coq.env.add-section-variable "LocalDefault" LD _.
}}.

Elpi Typecheck.
Elpi Export Contract. *)


Elpi Db implements_interface lp:{{

pred process_record i:term, i:term, i:record-decl, o:term, o:term.
process_record T RCon (field _ FN _ F) RT RC  :- coq.say "field" FN,
                                                 get_name FN FNT,
                                                 RCon1 = {{ lp:RCon lp:FNT }},   
                                                 process_record T RCon1 (F _) RT RC.
process_record T RCon end-record T RCon.

pred add_parameter i:term, i:term, i:term , i:term, i:term , i:term, 
                   i:term, i:id, o:term.
add_parameter LR CT LTT VT MT LLCGR       T "ULValue" {{ lp:T (@ULValueL 
                                                                lp:LR 
                                                                lp:CT 
                                                                lp:LTT 
                                                                lp:VT 
                                                                lp:MT 
                                                                GlobalParamsLRecord 
                                                                OutgoingMessageParamsLRecord 
                                                                lp:LLCGR) }}.
add_parameter _ _ _ _ _ _  T N {{ lp:T lp:NT }} :- get_name N NT.      



pred add_parameters i:term, i:term, i:term , i:term, i:term , i:term, 
                    i:term, i:list id, o:term.
add_parameters LR CT LTT VT MT LLCGR T [P|PS] TT :- add_parameter  LR CT LTT VT MT LLCGR T P T1,
                                                   add_parameters LR CT LTT VT MT LLCGR T1 PS TT.   
add_parameters _ _ _ _ _ _ T [] T.

pred add_tail i:list X, i:X, o:list X.
add_tail [] X [X] :- !.
add_tail [H|T] X [H|TT] :- !, add_tail T X TT.

pred process_class i:term, i:term, i:term , i:term, i:term , i:term, 
                   i:term, i:indt-decl, o:term, i:list id, o:term.
/* id -> implicit_kind -> term -> (term -> indt-decl) -> indt-decl */
process_class LR CT LTT VT MT LLCGR T (parameter PN _ _ F) RT IC RC :- 
                                      coq.say "parameter" PN,
                                      add_parameter LR CT LTT VT MT LLCGR T PN T1,
                                      add_tail IC PN IC1, 
                                      process_class LR CT LTT VT MT LLCGR T1 (F _) RT IC1 RC.
process_class LR CT LTT VT MT LLCGR T (record RN _ RCN F) RT IC RC :- coq.say "class" RN,
                                                                get_name RCN RCon,
                                                                add_parameters LR CT LTT VT MT LLCGR  RCon IC RCon1,
                                                                process_record T RCon1 F RT RC. 

pred implements_interface i:list argument.
implements_interface [str A] :- 
get_name "ContractLRecord" CT,
get_name "LedgerLRecord"  LR,
get_name "MessagesAndEventsLRecord"  MT,
get_name "VMStateLRecord"  VT,
get_name "LocalStateLRecord"  LTT,
get_name "LedgerLLedgerClass" LLCGR,

coq.locate A AGR,
coq.arguments.name AGR Args,
coq.say Args,
ATrm = global AGR,
AGR = indt AInd,
coq.env.indt-decl AInd AIndDecl,
coq.say AIndDecl,
process_class LR CT LTT VT MT LLCGR ATrm AIndDecl ATrmFull [] AInst,
coq.say AInst ,
std.assert-ok! (coq.elaborate-skeleton ATrmFull _ _) "Error" ,
std.assert-ok! (coq.elaborate-skeleton AInst _ _) "Error" ,
AN is "'" ^ A ^ "'",
@global! => coq.notation.add-term-notation AN
                                           []
                                           (some "ursus_scope") 
                                           (none)
                                           (some 0)
                                           ATrmFull 
                                           ff _,
std.assert-ok! (coq.elaborate-skeleton {{ lp:AInst : lp:ATrmFull }} TY Body) "Error" , 
IN is A ^ "Implemeted",                                           
coq.env.add-const IN Body TY @transparent! _ ,
coq.locate IN INGR,
@global! => coq.TC.declare-instance INGR 0.

}}.

Elpi Command Implements.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db implements_interface.

Elpi Accumulate lp:{{ 

main [A] :- implements_interface [A].

}}.

Elpi Typecheck.
Elpi Export Implements.


Elpi Command MakeInterface.

Elpi Accumulate Db global_fields_utils.

Elpi Accumulate lp:{{ 

pred add_tail i:list X, i:X, o:list X.
add_tail [] X [X] :- !.
add_tail [H|T] X [H|TT] :- !, add_tail T X TT.

pred co_replace i:term, i:term, i:term, o:term.
co_replace ULV (prod A {{lp:ULV lp:AT}} F) I (prod A AT (_ \ R)) :- co_replace ULV (F _) I R.
co_replace ULV (prod A AT F) I (prod A AT (_ \ R)) :- co_replace ULV (F _) I R.
co_replace _ _ I I.

pred process_record i:term, i:record-decl, o:term -> list indc-decl.
process_record ULV (field _ FN FT F) RR1  :- coq.say "field" FN FT,
                                          (CN is "_" ^ FN), 
                                          (RR1 = i \ [ constructor CN (arity {co_replace ULV FT i} ) | RR i ]),
                                          process_record ULV (F _) RR.
process_record _ end-record (_ \ []).

pred process_class i:term, i:indt-decl, i:list id, o:indt-decl.
process_class ULV (parameter _PN _ _ F) PL ANewInd :- process_class ULV (F _) PL ANewInd.
process_class ULV (record RN _ _RCN F) _PL (inductive RN tt (arity {{Type}}) i \ (RR i)) :-  
                    process_record ULV F RR.                                                      

main [ indt-decl A ] :- 
A = record N T C F,
std.assert-ok! (coq.typecheck-indt-decl A) "error", /* to set universes */
get_name "ULValue" ULV, 
NN is N ^ "Class",
CC is C ^ "Class",
AA = record NN T CC F,
coq.env.add-indt AA AI,
AGR = indt AI,
coq.TC.declare-class AGR,
process_class ULV A [] ANewInd ,
std.assert-ok! (coq.typecheck-indt-decl ANewInd) "error", /* to set universes */
coq.env.add-indt ANewInd _.
}}.

Elpi Typecheck.
Elpi Export MakeInterface.

Elpi Command Interfaces.

Elpi Accumulate Db global_fields_utils.

Elpi Accumulate lp:{{ 

main [ ] :- 
  SN = "Interfaces",
  coq.env.begin-section SN,
  coq.env.add-section-variable "ULValue" {{ Type -> Type }} _ ,
  coq.env.add-section-variable "public" {{Type -> bool -> Type}} _,
  coq.env.add-section-variable "external" {{Type -> bool -> Type}} _.
}}.

Elpi Typecheck.
Elpi Export Interfaces.

Elpi Command EndInterfaces.

Elpi Accumulate Db global_fields_utils.

Elpi Accumulate lp:{{ 

main [] :- coq.env.end-section.

}}.

Elpi Typecheck.

Elpi Export EndInterfaces.

Elpi Command EndContract.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db implements_interface.

Elpi Accumulate lp:{{ 

pred implements_interfaces i:list argument.
implements_interfaces [str I|IXS] :- 
                                 IC is I ^ "Class", 
                                 implements_interface [str IC],
                                 implements_interfaces IXS.
implements_interfaces [] :- !.                                 

pred main i:list argument.
main [str "Implements"|IL] :- 
  coq.say IL,
  implements_interfaces IL, 
  coq.env.end-section.

main [] :- 
  coq.env.end-section.

main _ :- coq.error "Syntax error".

}}.

Elpi Typecheck.

Elpi Export EndContract.


Elpi Db outgoing_interfaces lp:{{

pred make_fields i:list argument, i:record-decl, o:record-decl.
make_fields [str F|FS] T R :-   get_name F FI,
                            (N is "OutgoingMessages_" ^ F),
                            (R = field [] N {{messageQueue lp:FI}} _ \ X ),
                            make_fields FS T X. 
make_fields [] R R. 

pred make_outgoing_interfaces i:list argument.
make_outgoing_interfaces AL :- coq.say AL,
  (R = record "MessagesAndEvents" {{ Type }} "Build_MessagesAndEvents" RDecl),
  (Rest = field [] "EmittedEvents" {{XList TVMEvent}} _ \
        field [] "GlobalParams" {{GlobalParamsLRecord}} _ \
        field [] "OutgoingMessageParams" {{OutgoingMessageParamsLRecord}} _ \
        field [] "MessagesLog" {{XList string}} _ \
        end-record),
  (RDecl = field [] "OutgoingMessages_IDefault" {{_defqueue messageQueue IDefault}} _ \
          {make_fields AL Rest}),
  std.assert-ok! (coq.typecheck-indt-decl R) "error",
  std.assert-ok! (coq.elaborate-indt-decl-skeleton R R1) "illtyped",
  R1 = record N _ _ FDecl,
  generate_record_internals N FDecl NF NTL _,
  global_generate_pruvendo_record NTL NF _.

}}.

Elpi Command OutgoingInterfaces.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db generate_record_internals.
Elpi Accumulate Db global_generate_pruvendo_record. 
Elpi Accumulate Db outgoing_interfaces.

Elpi Accumulate lp:{{ 

pred main i:list argument.
main AL :- make_outgoing_interfaces AL.

}}.

Elpi Typecheck.

Elpi Export OutgoingInterfaces.

Elpi Command Contract.

Elpi Accumulate Db global_fields_utils.
Elpi Accumulate Db generate_record_internals.
Elpi Accumulate Db global_generate_pruvendo_record. 
Elpi Accumulate Db local_generate_pruvendo_record.
Elpi Accumulate Db outgoing_interfaces.
Elpi Accumulate Db declare_contract_internals.
Elpi Accumulate Db make_message_queue.
Elpi Accumulate Db string_utils.

Elpi Accumulate lp:{{ 

pred start_contract i:string.
start_contract A :- 
  SN is A ^ "Section",
  coq.env.begin-section SN,
  coq.env.add-section-variable "LocalStateLRecord" {{ Type (* @{XDefault.u0} *) }} LC,
  LCT = global (const LC),
  LD = {{XDefault lp:LCT}},
  coq.typecheck LD _ _, /* to avoid universes information incompleteness */
  coq.env.add-section-variable "LocalDefault" LD _.

pred add_constant i:id, i:term, i:arity.
add_constant N Bo A :-
coq.arity->term A Ty, 
get_name "ContractLRecord" CT,
get_name "LedgerLRecord"  LR,
get_name "MessagesAndEventsLRecord"  MT,
get_name "VMStateLRecord"  VT,
get_name "LocalStateLRecord"  LT,
get_name "LedgerLLedgerClass" LLCGR,

std.assert-ok! (coq.elaborate-skeleton {{  @sInjectL lp:LR lp:CT lp:LT lp:VT lp:MT GlobalParamsLRecord 
                                            OutgoingMessageParamsLRecord lp:LLCGR lp:Ty lp:Bo }} TY Body) "Error" ,
NR is N ^ "_right",                                            
@global! => coq.env.add-const NR Body TY @transparent! _,  
get_name NR NRT,                                           
NN is "'" ^ N ^ "'",                                            
@global! => coq.notation.add-notation NN 
                    []
                    (some "ursus_scope") 
                    (some "URValue")
                    (some 0)
                    NRT 
                    ff _ .

pred add_constants i:list argument.
add_constants [].
add_constants [const-decl N (some Bo) Ty | Args] :-
 add_constant N Bo Ty,
 add_constants Args.


pred add_record i:indt-decl.
add_record R :-
  std.assert-ok! (coq.elaborate-indt-decl-skeleton R R1) "illtyped",
  R1 = record N _ _ FDecl,
  local_generate_record_internals N FDecl NF NTL _,
  local_generate_pruvendo_record NTL NF _.

pred add_types i:list argument.
add_types [].
add_types [indt-decl R | Args] :-
 add_record R,
 add_types Args. 


pred proceed_contract i:int, /* step */
                      i:list argument, /* All */
                      i:list argument, /* Sends */
                      i:list argument, /* Inherits */
                      i:list argument, /* Types */
                      i:list argument, /* Constants */
                      i:list argument. /* Contract Record */
proceed_contract 0 [str ";"|XS] _ _ _ _ _ :- proceed_contract 1 XS [] [] [] [] [].
proceed_contract 0 _            _ _ _ _ _ :- coq.error "Syntax error 0".

proceed_contract 1 [str "Sends"|XS]     _ _ _ _ _ :- proceed_contract 2 XS [] [] [] [] [].  /* 2,3 - Sends */
proceed_contract 1 [str "Inherits"|XS]  _ _ _ _ _ :- proceed_contract 4 XS [] [] [] [] [].  /* 4 - Inherits */
proceed_contract 1 [str "Types"|XS]     _ _ _ _ _ :- proceed_contract 5 XS [] [] [] [] [].  /* 5 - Types */
proceed_contract 1 [str "Constants"|XS] _ _ _ _ _ :- proceed_contract 6 XS [] [] [] [] [].  /* 6 - Constants */
proceed_contract 1 [R]                  _ _ _ _ _ :- proceed_contract 7 [] [] [] [] [] [R]. /* 7 - Main Record */
proceed_contract 1 _                    _ _ _ _ _ :- coq.error "Syntax error 1".

proceed_contract 2 [str "To"|XS]        _ _ _ _ _ :- proceed_contract 3 XS [] [] [] [] [].
proceed_contract 2 _                    _ _ _ _ _ :- coq.error "Syntax error 2".

proceed_contract 3 [str ";" , str "Inherits" | XS] Sends _ _ _ _ :- proceed_contract 4 XS Sends [] [] [] [].
proceed_contract 3 [str ";" , str "Types"    | XS] Sends _ _ _ _ :- proceed_contract 5 XS Sends [] [] [] [].
proceed_contract 3 [str ";" , str "Constants"| XS] Sends _ _ _ _ :- proceed_contract 6 XS Sends [] [] [] [].
proceed_contract 3 [str ";" , R]                   Sends _ _ _ _ :- proceed_contract 7 [] Sends [] [] [] [R].
proceed_contract 3 [str N|XS]                      Sends _ _ _ _ :- proceed_contract 3 XS {add_tail Sends (str N)} [] [] [] [].
proceed_contract 3 _                               _     _ _ _ _ :- coq.error "Syntax error 3".

proceed_contract 4 [str ";" , str "Types"    | XS] Sends Inherits _ _ _ :- proceed_contract 5 XS Sends Inherits [] [] [].
proceed_contract 4 [str ";" , str "Constants"| XS] Sends Inherits _ _ _ :- proceed_contract 6 XS Sends Inherits [] [] [].
proceed_contract 4 [str ";" , R]                   Sends Inherits _ _ _ :- proceed_contract 7 [] Sends Inherits [] [] [R].
proceed_contract 4 [str N|XS]                      Sends Inherits _ _ _ :- proceed_contract 4 XS Sends {add_tail Inherits (str N)} [] [] [].
proceed_contract 4 _ _ _ _ _ _ :- coq.error "Syntax error 4".


proceed_contract 5 [str ";" , str "Constants"| XS] Sends Inherits Types _ _ :- proceed_contract 6 XS Sends Inherits Types     [] [].
proceed_contract 5 [str ";" , R]                   Sends Inherits Types _ _ :- proceed_contract 7 [] Sends Inherits Types     [] [R].
proceed_contract 5 [indt-decl R|XS]                Sends Inherits Types _ _ :- proceed_contract 5 XS Sends Inherits {add_tail Types (indt-decl R)} [] [].
proceed_contract 5 _ _ _ _ _ _ :- coq.error "Syntax error 5".


proceed_contract 6 [str ";" , R]      Sends Inherits Types Constants _ :- proceed_contract 7 [] Sends Inherits Types Constants [R].
proceed_contract 6 [const-decl N (some Bo) Ty |XS]  Sends Inherits Types Constants _ :- proceed_contract 6 XS Sends Inherits Types {add_tail Constants (const-decl N (some Bo) Ty)} [].
proceed_contract 6 _                  _     _        _     _         _ :- coq.error "Syntax error 6".

proceed_contract 7 [] Sends Inherits Types Constants [indt-decl R] :- 
    coq.say  "Types = " Types,
    coq.say  "Constants = " Constants,
    add_types Types,
    make_outgoing_interfaces Sends,
    (R = record RId RTy CId RDecl),
    add_inherited Inherits RDecl RDecl1,
    (R1 = record RId RTy CId RDecl1),
    declare_contract_internals (indt-decl R1),
    make_message_queue,
    add_constants Constants.
proceed_contract _ _ _ _ _ _ _ :- coq.error "Syntax error 7".

pred add_inherited i:list argument, i:record-decl, o:record-decl.
add_inherited [str I|IS] R R1 :-
  (FS is "_" ^ I ^ "_inherited"),
  (FTS is I ^ ".ContractLRecord"),
  get_name FTS FT,
  (RR = field  [coercion ff, canonical tt] FS FT x \ R),
  add_inherited IS RR R1.
add_inherited [] R R.

pred main i:list argument.
main [str A | T] :- start_contract A ,
                    proceed_contract 0 T [] [] [] [] [].
 
}}.

Elpi Typecheck.
Elpi Export Contract.

Elpi Command UseLocal.

Elpi Accumulate Db global_fields_utils.

Elpi Accumulate lp:{{ 

pred add_one_local_context i:term.
add_one_local_context T :-
get_name "LocalStateLRecord" LSLR,
coq.env.add-context none {{
      LocalStateField XHMap lp:LSLR lp:T
    }} tt tt.

pred add_local_context i:term.
add_local_context {{ []%glist }}.
add_local_context {{ []%llist }}.
add_local_context {{ (lp:H :: lp:TL)%glist }} :-
  add_one_local_context H,
  add_local_context TL.
add_local_context {{ (lp:H :: lp:TL)%llist }} :-
  add_one_local_context H,
  add_local_context TL.
add_local_context T :-
  coq.typecheck T {{Type}} _,
  add_one_local_context T.
add_local_context T :-  coq.error "not implemented: " T.

main [const-decl _N (some Bo) _Ty] :-
  add_local_context Bo.
main Arg :- coq.error "Error in argument: " Arg.

}}.

Elpi Typecheck.
Elpi Export UseLocal.

Ltac unfold_ x := unfold x.

Elpi Tactic unfold_mod.

Elpi Accumulate Db global_fields_utils.

Elpi Accumulate lp:{{
 
  solve (goal _ _ _ _ _ as G) GL :-
    get_name "modifier" X,
    coq.ltac.call "unfold_" [trm X] G GL.

  solve _ _ :- coq.ltac.fail _ 
    "unfold_mod failed, see debug output for details".
}}.
Elpi Typecheck.

Tactic Notation "unfold_mod" := (elpi unfold_mod; intros X b u).


