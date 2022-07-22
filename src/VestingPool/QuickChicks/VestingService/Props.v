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

Require Import UrsusStdLib.Solidity.All.

Require Import UrsusTVM.Solidity.tvmTypes.
Require Import UrsusTVM.Solidity.tvmFunc.
Require Import UrsusTVM.Solidity.tvmNotations.
Require Import UrsusTVM.Solidity.tvmCells.

Require Import UrsusDefinitions.
Require Import UrsusDefinitions2.


Import UrsusNotations.
Local Open Scope xlist_scope.
Local Open Scope record.
Local Open Scope program_scope.
Local Open Scope glist_scope.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.

From elpi Require Import elpi.


Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Require Import VestingPool.Modifiers. (*contract*)
Require Export VestingPool.VestLib. (*library*)
Require Import VestingPool.interfaces.IVestingPool. (*interface*)
Require Import VestingPool.interfaces.IOnPoolActivated. (*interface*)
Require Import VestingPool.VestingService.
Import VestingServiceContract.

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import FinProof.CommonInstances.


Require Import LocalState.VestingService.
Notation rec := LocalStateLRecord.
Definition computed : LocalStateLRecord  := Eval compute in default. 
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 
Definition VMStateDefault : VMStateLRecord  := Eval compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval compute in default. 

(*New pool can be created  by anybody, after being addressed as Creator*)
Definition GVS_01 l (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  mapping uint256 uint256) 
  : Prop :=
let l' := exec_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l in
toValue (eval_state (sRReader || msg->sender  || ) l') = default ->
isError (eval_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l) = true.

(* Anybody non-empty can be included into the client public key list *)
Definition GVS_02 l (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers claimers' :  mapping uint256 uint256)
  : Prop :=
isError (eval_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l) = false ->
(* TODO claimers->length() = 0 ->
claimers->length() < MAX -> *)
isError (eval_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers')) l) = false.

 (*At least one client must exists*)
Definition GVS_03 l (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  mapping uint256 uint256)
  : Prop :=
(* TODO claimers->length() = 0 ->
 *) isError (eval_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l) = true.

Definition GVS_05 l (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient recipient' :  address) (claimers  :  mapping uint256 uint256)
  : Prop :=
isError (eval_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l) = false ->
uint2N (snd recipient') =  0 ->
(* TODO int2N ((recipient')->wid) = 0 -> *)
isError (eval_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient' claimers)) l) = false.

(*GVS_06 in VestingPool *)
 (*If all the input is correct a new VestingPool is created*)
Definition GVS_07 l  addr (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  mapping uint256 uint256)
  : Prop :=
 let claimersMap := toValue (eval_state (Uinterpreter  (createClaimersMap rec def claimers) ) l) in 
 let mes_cons := (IVestingPool._constructor amount cliffMonths vestingMonths recipient claimersMap) in
 let mes := OutgoingInternalMessage  (Build_XUBInteger 0, (true, Build_XUBInteger 64)) mes_cons  in
 let l' := exec_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l in
 isError (eval_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l) = false ->
 (* ?TODO GVS_08_1  address = address (_nextId)*)
 isMessageSent mes addr 0 
   (toValue (eval_state (sRReader (ULtoRValue (IVestingPool_left rec def))) l')) = true.
 
Definition GVS_08 l (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  mapping uint256 uint256)
  : Prop :=
let l' := exec_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l in
let _nextId := toValue (eval_state (sRReader (m_nextId_right rec def) ) l) in
let _nextId' := toValue (eval_state (sRReader (m_nextId_right rec def) ) l') in
isError (eval_state (Uinterpreter (createPool rec def amount cliffMonths vestingMonths recipient claimers)) l) = false ->
uint2N _nextId' > uint2N _nextId.

(* ?TODO GVS_08_1  address = address (_nextId)*)
