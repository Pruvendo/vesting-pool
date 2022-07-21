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
Require Import VestingService.QCEnvironment.
Require Import VestingService.Props.

Require Import VestingPool.VestingService.
Import VestingServiceContract.

Definition GVS_01_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 uint256)
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

GVS_01 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient claimers ? .

Definition GVS_03_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 uint256)
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

GVS_03 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient claimers ? .

Definition GVS_05_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient recipient':  address) 
    (claimers :  mapping uint256 uint256)
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

GVS_05 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient recipient' claimers ? .


Definition GVS_07_propb l
      (addr : address)
      (amount :  uint128) 
      (cliffMonths :  uint8) 
      (vestingMonths :  uint8) 
      (recipient :  address) 
      (claimers :  mapping uint256 uint256)
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
   
   GVS_07 {$$ 
           {$$ LedgerDefault with Ledger_MainState := l $$}
                               with Ledger_VMState := v5 $$}
        addr amount cliffMonths vestingMonths recipient claimers ? .

Definition GVS_08_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  address) 
    (claimers :  mapping uint256 uint256)
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

GVS_08 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths recipient claimers ? .

(*
Extract Constant defNumTests => "10000".
Extract Constant defSize => "7".

Time QuickCheck GVS_01_propb.
(* ???*) (*Time QuickCheck GVS_02_propb.*)
(* should fail: isError = true *) Time QuickCheck GVS_03_propb.
(* should fail *) Time QuickCheck GVS_05_propb.
(* should fail*) Time QuickCheck GVS_07_propb.
Time QuickCheck GVS_08_propb.
*)