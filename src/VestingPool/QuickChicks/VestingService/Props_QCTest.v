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
    (recipient :  XUBInteger 256) 
    (claimers :  mapping uint256 uint256)
    ( ms: address )
    ( mv: N )
    ( addr: address ) : bool :=
let v3 := {$$ VMStateDefault with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_address := addr $$} in

GVS_01 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths  (0%Z, recipient) claimers ? .

(* TODO: sender should be default? *)
(*QuickCheck GVS_01_propb.*)

Definition GVS_02_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  XUBInteger 256) 
    (claimers :  mapping uint256 uint256)
    (claimers' :  mapping uint256 uint256)
    ( ms: address )
    ( mv: N )
    ( addr: address ) : bool :=
let v3 := {$$ VMStateDefault with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_address := addr $$} in

GVS_02 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths  (0%Z, recipient) claimers claimers' ? .

(* TODO: passes -- strange, probably should fail *)
(*QuickCheck GVS_02_propb.*)

Definition GVS_03_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  XUBInteger 256) 
    (claimers :  mapping uint256 uint256)
    ( ms: address )
    ( mv: N )
    ( addr: address ) : bool :=
let v3 := {$$ VMStateDefault with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_address := addr $$} in

GVS_03 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths (0%Z, recipient) claimers ?.

(* fails -- as it should *)
(*QuickCheck GVS_03_propb.*)

Definition GVS_05_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient recipient':  XUBInteger 256) 
    (claimers :  mapping uint256 uint256)
    ( ms: address )
    ( mv: N )
    ( addr: address )  : bool :=
let v3 := {$$ VMStateDefault with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_address := addr $$} in
    
GVS_05 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths (0%Z, recipient) (0%Z, recipient') claimers ? .

(* fails -- it probably should, need to investigate*)
(*QuickCheck GVS_05_propb.*)

Definition GVS_07_propb l
      (addr : address)
      (amount :  uint128) 
      (cliffMonths :  uint8) 
      (vestingMonths :  uint8) 
      (recipient :  XUBInteger 256) 
      (claimers :  mapping uint256 uint256)
      ( ms: address )
      ( mv: N )
      ( tvm_addr: address )  : bool :=
let v3 := {$$ VMStateDefault with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_address := tvm_addr $$} in
           
   GVS_07 {$$ 
           {$$ LedgerDefault with Ledger_MainState := l $$}
                               with Ledger_VMState := v5 $$}
        addr amount cliffMonths vestingMonths (0%Z, recipient) claimers ? .

(* fails, need to investigate*)
(*QuickCheck GVS_07_propb.*)

Definition GVS_08_propb l
    (amount :  uint128) 
    (cliffMonths :  uint8) 
    (vestingMonths :  uint8) 
    (recipient :  XUBInteger 256) 
    (claimers :  mapping uint256 uint256)
    ( ms: address )
    ( mv: N )
    ( addr: address ) : bool :=
let v3 := {$$ VMStateDefault with VMState_ι_msg_sender := ms $$} in
let v4 := {$$ v3 with VMState_ι_msg_value := Build_XUBInteger (10 * mv) $$} in
let v5 := {$$ v4 with VMState_ι_address := addr $$} in
    
GVS_08 {$$ 
        {$$ LedgerDefault with Ledger_MainState := l $$}
                            with Ledger_VMState := v5 $$}
       amount cliffMonths vestingMonths (0%Z, recipient) claimers ? .

(*QuickCheck GVS_08_propb.*)