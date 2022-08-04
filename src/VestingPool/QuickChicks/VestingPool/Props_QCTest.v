Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.
Require Import Coq.Program.Equality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21.
Require Import FinProof.Common.
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

Require Import UrsusTVM.Solidity.tvmTypes.
Require Import UrsusTVM.Solidity.tvmFunc.
Require Import UrsusTVM.Solidity.tvmNotations.

(* Require Import Blank.ClassTypesNotations. *)

(* Set Typeclasses Depth 100. *)

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

(* 

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.
 *)
Require Import Logic.FunctionalExtensionality.
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import CommonQCEnvironment.
Require Import VestingPool.QCEnvironment.
Require Import VestingPool.Props.

Require Import VestingPool.VestingPool.
Import VestingPoolContract.

Require Import UMLang.ExecGenerator.

Definition GVS_06_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    ( nw : uint32 )
    ( ms: address )
    ( mv: N )
    (bal: N): bool :=
let v2 := {$$ VMStateDefault with VMState_ι_now := nw $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in
GVS_06 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient claimers ? .

(* ok *)
QuickCheck GVS_06_propb.

Definition GVS_09_propb l
    (amount :  uint128)
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    (dt : N) 
    (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_09 {$$ 
         {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient claimers (dt * 15 * 86400) ? .

(* ok *)
QuickCheck GVS_09_propb.

Definition GVS_10_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    (dt : N) 
    (bal: N) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_10 {$$ 
     {$$ LedgerDefault with Ledger_MainState := l $$}
                with Ledger_VMState := v5 $$}
   amount cliffMonths vestingMonths recipient claimers (dt * 15 * 86400) ? .

(* ok *)
QuickCheck GVS_10_propb.

Definition GVS_11_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    (bal: N ):=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in
GVS_11 {$$ 
    {$$ LedgerDefault with Ledger_MainState := l $$}
                        with Ledger_VMState := v5 $$}
    amount cliffMonths vestingMonths recipient claimers ? .

(* ok *)
QuickCheck GVS_11_propb.

(* some valid input data -- keep it here just in case

Import ListNotations.

Definition l : (XUBInteger 256 *
(Z * XUBInteger 256 *
 (XUBInteger 32 *
  (XUBInteger 32 *
   (XUBInteger 32 *
    (XUBInteger 32 *
     (XUBInteger 128 *
      (XUBInteger 128 *
       (XUBInteger 128 *
        (Z * XUBInteger 256 *
         CommonInstances.ListStructure (XUBInteger 256 * bool)
           CommonInstances.Map)%xprod)%xprod)%xprod)%xprod)%xprod)%xprod)%xprod)%xprod)%xprod)%xprod := 
    xpair (Build_XUBInteger 0) (xpair (0%Z,Build_XUBInteger 0) 
    (xpair (Build_XUBInteger 0) (xpair (Build_XUBInteger 0) (xpair (Build_XUBInteger 0) (xpair (Build_XUBInteger 0) (xpair (Build_XUBInteger 0) (xpair (Build_XUBInteger 0) (xpair (Build_XUBInteger 0) (xpair (0%Z,(Build_XUBInteger 0)) (CommonInstances.wrap _ ([((Build_XUBInteger 4),false); ((Build_XUBInteger 2),false); ((Build_XUBInteger 1),false); ((Build_XUBInteger 0),false)])%list)))))))))).
Compute address.
Definition addr : address := (0%Z, Build_XUBInteger 0).
Definition v4 := let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := Build_XUBInteger 0 $$} in     
let v1 := {$$ v0 with VMState_ι_now := Build_XUBInteger 0 $$} in
let v2 := {$$ v1 with VMState_ι_accepted := true $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := (0%Z,Build_XUBInteger 1) $$} in
{$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * 5) $$}.

Definition lx := {$$ 
{$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v4 $$}.
Definition l' := launch lx
(Build_XUBInteger 5) (Build_XUBInteger 3) (Build_XUBInteger 0)
 addr (CommonInstances.wrap CommonInstances.Map ([::])%list).
Compute l'.
Compute (isError (eval_state (Uinterpreter (constructor rec def 
(Build_XUBInteger 5) (Build_XUBInteger 3) (Build_XUBInteger 0)
 addr (CommonInstances.wrap CommonInstances.Map ([::])%list))) lx)).
 Compute (uint2N (toValue (eval_state (sRReader (now) ) l'))).
Compute (uint2N (toValue (eval_state (sRReader (m_vestingEnd_right rec def) ) l'))).

Compute GVS_11_propb l 
    (Build_XUBInteger 5) (Build_XUBInteger 3) (Build_XUBInteger 0)
    (0%Z, Build_XUBInteger 0) (CommonInstances.wrap CommonInstances.Map ([::])%list)
    (Build_XUBInteger 0) (Build_XUBInteger 1) true (0%Z, Build_XUBInteger 1) 4.
QuickCheck GVS_11_propb.
*)

Definition GVS_12_1_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    (dt : N) 
    (bal: N) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_12_1 {$$ 
            {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
        amount cliffMonths vestingMonths recipient claimers (dt * 15 * 86400) ? .

(* ok *)
QuickCheck GVS_12_1_propb.

Definition GVS_12_2_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    (dt : N) 
    (bal: N) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_12_2 {$$ 
            {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
        amount cliffMonths vestingMonths recipient claimers (dt * 15 * 86400) ? .

(* ok *)
QuickCheck GVS_12_2_propb.

Definition GVS_13_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    n
    (dt : N) 
    (bal: N) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_13 {$$ 
            {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
        amount cliffMonths vestingMonths recipient claimers n (dt * 15 * 86400) ? .

(* ok*)
QuickCheck GVS_13_propb.

Definition GVS_14_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    ( dt : N )
    (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_14 {$$ 
            {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
        amount cliffMonths vestingMonths recipient claimers  (dt * 15 * 86400)  ? .

(* ok *)
QuickCheck GVS_14_propb.

Definition GVS_15_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    (dt : N) 
    (bal: N) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_15 {$$ 
            {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
        amount cliffMonths vestingMonths recipient claimers (dt * 15 * 86400) ? .

(* ok *)
QuickCheck GVS_15_propb.

Definition GVS_16_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    (dt : N) 
    (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_16 {$$ 
            {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
        amount cliffMonths vestingMonths recipient claimers (dt * 15 * 86400) ? .

(* ok *)
QuickCheck GVS_16_propb.

Definition GVS_17_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    ( dt : N)
    (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_17 {$$ 
            {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
        amount cliffMonths vestingMonths recipient claimers (dt * 15 * 86400) ? .

(* ok *)
QuickCheck GVS_17_propb.

Definition GVS_18_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    (mpk: uint256)
    (nw: uint32)
    (acc : bool)
    ( ms: address )
    ( mv: N )
    value 
    (dt : N)
    (bal: N): bool :=
let v0 := {$$ VMStateDefault with VMState_ι_msg_pubkey := mpk $$} in     
let v1 := {$$ v0 with VMState_ι_now := nw $$} in
let v2 := {$$ v1 with VMState_ι_accepted := acc $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_balance := Build_XUBInteger (10 * (mv + bal)) $$} in

GVS_18 {$$ 
            {$$ LedgerDefault with Ledger_MainState := l $$}
                    with Ledger_VMState := v5 $$}
        amount cliffMonths vestingMonths recipient claimers value (dt * 15 * 86400) ? .

(* ok *)
QuickCheck GVS_18_propb.