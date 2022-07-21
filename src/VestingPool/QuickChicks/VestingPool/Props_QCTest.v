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

Definition GVS_06_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    ( pk: uint256 )
    ( mpk: uint256) 
    ( mn : uint32 )
    ( ms: address )
    ( mv: uint128 )
    ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_ι_balance := tb $$} in
GVS_06 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient claimers ? .

Definition GVS_09_propb l
    (poolId : uint256) : bool :=
GVS_09 {$$ LedgerDefault with Ledger_MainState := l $$}
       poolId ? .

Definition GVS_10_propb l
    (poolId : uint256) : bool :=
GVS_10 {$$ LedgerDefault with Ledger_MainState := l $$}
       poolId ? .

Definition GVS_11_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    ( pk: uint256 )
    ( mpk: uint256) 
    ( mn : uint32 )
    ( ms: address )
    ( mv: uint128 )
    ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_ι_balance := tb $$} in
GVS_11 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient claimers ? .

Definition GVS_12_1_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 boolean)
    ( pk: uint256 )
    ( mpk: uint256) 
    ( mn : uint32 )
    ( ms: address )
    ( mv: uint128 )
    ( tb: uint128 ) : bool :=
let v0 := {$$ VMStateDefault with VMState_ι_pubkey := pk $$} in 
let v1 := {$$ v0 with VMState_ι_msg_pubkey := mpk $$} in     
let v2 := {$$ v1 with VMState_ι_now := mn $$} in
let v3 := {$$ v2 with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := mv $$} in
let v5 := {$$ v4 with VMState_ι_balance := tb $$} in
GVS_12_1 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient claimers ? .

Definition GVS_12_2_propb l
    (poolId : uint256) : bool :=
GVS_12_2 {$$ LedgerDefault with Ledger_MainState := l $$}
       poolId ? .

Definition GVS_13_propb l
    n (poolId : uint256) : bool :=
GVS_13 {$$ LedgerDefault with Ledger_MainState := l $$}
       n poolId ? .

Definition GVS_14_propb l
    (poolId : uint256) : bool :=
GVS_14 {$$ LedgerDefault with Ledger_MainState := l $$}
       poolId ? .

Definition GVS_15_propb l
    (poolId : uint256) : bool :=
GVS_15 {$$ LedgerDefault with Ledger_MainState := l $$}
       poolId ? .

Definition GVS_16_propb l
    (poolId : uint256) : bool :=
GVS_16 {$$ LedgerDefault with Ledger_MainState := l $$}
       poolId ? .

Definition GVS_17_1_propb l
    (poolId : uint256) : bool :=
GVS_17_1 {$$ LedgerDefault with Ledger_MainState := l $$}
       poolId ? .

Definition GVS_18_propb l
    value (poolId : uint256) : bool :=
GVS_18 {$$ LedgerDefault with Ledger_MainState := l $$}
       value poolId ? .

(*
Extract Constant defNumTests => "10000".
Extract Constant defSize => "7".

Time QuickCheck GVS_06_propb.
Time QuickCheck GVS_09_propb.
Time QuickCheck GVS_10_propb.
Time QuickCheck GVS_11_propb.
Time QuickCheck GVS_12_1_propb.
Time QuickCheck GVS_12_2_propb.
Time QuickCheck GVS_13_propb.
Time QuickCheck GVS_14_propb.
Time QuickCheck GVS_15_propb.
Time QuickCheck GVS_16_propb.
Time QuickCheck GVS_17_1_propb.
Time QuickCheck GVS_18_propb.
*)