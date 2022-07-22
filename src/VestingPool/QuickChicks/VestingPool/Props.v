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
Require Import VestingPool.VestingPool.
Import VestingPoolContract.

Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import FinProof.CommonInstances.

Require Import LocalState.VestingPool.
Notation rec := LocalStateLRecord.
Definition computed : LocalStateLRecord  := Eval compute in default. 
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 
Definition VMStateDefault : VMStateLRecord  := Eval compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval compute in default. 

(*The value of pool creation must cover the vesting amount as well as following fee : for pool creation, for each claim, for storage*)
Definition GVS_06 l (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean ))
  : Prop := 
uint2N (toValue (eval_state (sRReader || msg->value  || ) l)) <
uint2N  amount  + 
 uint2N (toValue (eval_state (sRReader (CONSTRUCTOR_GAS_right rec def) ) l)) + 
 uint2N (toValue (eval_state (sRReader (STORAGE_FEE_right rec def) ) l)) + 
uint2N (toValue (eval_state (sRReader (FEE_CLAIM_right rec def) ) l)) * uint2N vestingMonths  -> 
isError (eval_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) l) = true.

Definition launch lst (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean ))  :=
exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst. 
  
(*A list of clients can not be updated after the pool is created*)
Definition GVS_09 lst (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) (poolId : uint256) : Prop :=
let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
let l' := exec_state (Uinterpreter (claim rec def poolId)) l in
let _claimers := toValue (eval_state (sRReader (m_claimers_right rec def)) l) in
let _claimers' := toValue (eval_state (sRReader (m_claimers_right rec def)) l') in
_claimers = _claimers'.

(*A  receiver of funds can not be updated after the pool is created.*)
Definition GVS_10 lst (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) (poolId : uint256) : Prop :=
let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
let l' := exec_state (Uinterpreter (claim rec def poolId)) l in
let _recipient := toValue (eval_state (sRReader (m_recipient_right rec def) ) l) in
let _recipient' := toValue (eval_state (sRReader (m_recipient_right rec def) ) l') in
_recipient = _recipient'.

(*Vesting pool parameters must be initialized by the constructor*)
Definition GVS_11 l (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean ))
  : Prop := 
let l' := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) l in
isError (eval_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) l) = false ->
(* m_createdAt = params.now *)
toValue (eval_state (sRReader (m_createdAt_right rec def) ) l') = toValue (eval_state (sRReader || (now) || ) l) /\
(* m_recipient = params.recipient *)
toValue (eval_state (sRReader (m_recipient_right rec def) ) l') = recipient /\
(* m_claimers = claimers *)
toValue (eval_state (sRReader (m_claimers_right rec def) ) l') = claimers /\
(* m_cliffEnd = params.now + params.cliffMonths * 30 * 86400 *)
uint2N (toValue (eval_state (sRReader (m_cliffEnd_right rec def) ) l')) = uint2N (toValue (eval_state (sRReader || (now) || ) l)) + uint2N (cliffMonths)*30*86400 /\
(* m_vestingEnd = params.now + (params.cliffMonths + params.vestingMonths) * 30 * 86400 *)
uint2N (toValue (eval_state (sRReader (m_vestingEnd_right rec def) ) l')) = uint2N (toValue (eval_state (sRReader || (now) || ) l)) + (uint2N (cliffMonths) + uint2N (vestingMonths))*30*86400 /\
(* m_totalAmount = params.amount *)
toValue (eval_state (sRReader (m_totalAmount_right rec def) ) l') = amount /\
(* m_remainingAmount = params.amount *)
toValue (eval_state (sRReader (m_remainingAmount_right rec def) ) l') = amount.

(*Funds are locked in the pool to return until the deadline of the open window.*)
Definition GVS_12_1 l (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean ))
  : Prop :=
isError (eval_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) l) = false ->
let l' := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) l in
uint2N (toValue (eval_state (sRReader || tvm->balance () || ) l')) > uint2N amount.

Definition GVS_12_2 lst  (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) (poolId : uint256) : Prop :=
let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
let l' := exec_state (Uinterpreter (claim rec def poolId)) l in
uint2N (toValue (eval_state (sRReader || tvm->balance () || ) l)) > uint2N (toValue (eval_state (sRReader (m_remainingAmount_right rec def) ) l)) ->
uint2N (toValue (eval_state (sRReader || tvm->balance () || ) l')) > uint2N (toValue (eval_state (sRReader (m_remainingAmount_right rec def) ) l')).

(*To prevent incorrect usage of the pool it can  transfer only once per time-slot after the first call. The  rest of calls to transfer within a time are rejected.  *)
(* TODO l' = l' with now' *)
Definition GVS_13 lst  (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) n (poolId : uint256) : Prop := 
let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
let l' := exec_state (Uinterpreter (claim rec def poolId)) l in
let _now := toValue (eval_state (sRReader || (now) || ) l) in
let _now' := toValue (eval_state (sRReader || (now) || ) l') in
let _VESTING_PERIOD := toValue (eval_state (sRReader (VESTING_PERIOD_right rec def) ) l) in
let _vestingFrom := toValue (eval_state (sRReader (m_vestingFrom_right rec def) ) l) in
isError (eval_state (Uinterpreter (claim rec def poolId)) l) = false ->
(uint2N _now > uint2N _vestingFrom + n* uint2N _VESTING_PERIOD) ->
(uint2N _now < uint2N _vestingFrom + (n+1)* uint2N _VESTING_PERIOD) ->
(uint2N _now' > uint2N _vestingFrom + n* uint2N _VESTING_PERIOD) ->
(uint2N _now' < uint2N _vestingFrom + (n+1)* uint2N _VESTING_PERIOD) ->
(uint2N _now <= uint2N _now') ->
isError (eval_state (Uinterpreter (claim rec def poolId)) l') = true.

(*Only claimers can claim *) 
Definition GVS_14 lst (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) (poolId : uint256) : Prop :=
let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
let _msgSender := toValue (eval_state (sRReader || msg->pubkey() || ) l) in
let _claimers := toValue (eval_state (sRReader (m_claimers_right rec def) ) l) in
 _claimers[_msgSender] = false ->
isError (eval_state (Uinterpreter (claim rec def poolId)) l) = true.

(* Any attempts to claim during the cliff period must lead to exception *)
Definition GVS_15 lst (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) (poolId : uint256) : Prop :=
let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
let _now := toValue (eval_state (sRReader || (now) || ) l) in
let _cliffEnd := toValue (eval_state (sRReader (m_cliffEnd_right rec def) ) l) in
(uint2N _now < uint2N _cliffEnd) ->
isError (eval_state (Uinterpreter (claim rec def poolId)) l) = true.

(*Any attempt to claim after vestingEnd must lead to sending the rest of the amount to the recipient and the change back to the creator. Also the pool must suicide itself.*)
(* TODO suicide
transfer to creator *)
Definition GVS_16 lst (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) (poolId : uint256) : Prop :=
 let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
 let l' := exec_state (Uinterpreter (claim rec def poolId)) l in
 let _now := toValue (eval_state (sRReader || (now) || ) l) in
 let _vestingEnd := toValue (eval_state (sRReader (m_vestingEnd_right rec def) ) l) in
 let addr := toValue (eval_state (sRReader (m_recipient_right rec def) ) l) in
 let value := (toValue (eval_state (sRReader (m_remainingAmount_right rec def) ) l)) in

 let mes := (EmptyMessage IDefault (value, (true, Build_XUBInteger 2))) in
 false = isError (eval_state (Uinterpreter (claim rec def poolId)) l) -> 
 (uint2N _now > uint2N _vestingEnd) ->
   isMessageSent mes addr 0 
   (toValue (eval_state (sRReader (ULtoRValue (IDefault_left rec def))) l')) = true.

 (* The remaining amount for each successful claim is decreased by the transfer amount to the recipient*)
Definition GVS_17_1 lst (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) (poolId : uint256) : Prop :=
 let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
 let l' := exec_state (Uinterpreter (claim rec def poolId)) l in
 let addr := toValue (eval_state (sRReader (m_recipient_right rec def) ) l) in
 let value := fst (toValue (eval_state (sRReader (calcUnlocked_right rec def ) ) l)) in
 let mes := (EmptyMessage IDefault (value, (true, Build_XUBInteger 2))) in
 false = isError (eval_state (Uinterpreter (claim rec def poolId)) l) -> 
   isMessageSent mes addr 0 
   (toValue (eval_state (sRReader (ULtoRValue (IDefault_left rec def))) l')) = true.

(* If the current time is after cliff period and before the vesting end (that effectively means that vesting period is more than zero) the amount to vest is calculated by the following formula*)
Definition GVS_18 lst (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )) value (poolId : uint256)
  : Prop :=
 let l := exec_state (Uinterpreter (constructor rec def amount cliffMonths vestingMonths recipient claimers)) lst in 
 let l' := exec_state (Uinterpreter (claim rec def poolId)) l in
 let addr := toValue (eval_state (sRReader (m_recipient_right rec def) ) l) in
 let _now := toValue (eval_state (sRReader || (now) || ) l) in
 let _cliffEnd := toValue (eval_state (sRReader (m_cliffEnd_right rec def ) ) l) in
 let _vestingEnd := toValue (eval_state (sRReader (m_vestingEnd_right rec def)) l) in
 let _vestingAmount := toValue (eval_state (sRReader (m_vestingAmount_right rec def) ) l) in
 let _vestingFrom := toValue (eval_state (sRReader (m_vestingFrom_right rec def) ) l) in
 let _VESTING_PERIOD := toValue (eval_state (sRReader (VESTING_PERIOD_right rec def) ) l) in
 let vestingPeriods :=  (( uint2N _now -  uint2N _vestingFrom) / uint2N _VESTING_PERIOD ) in
 let mes := (EmptyMessage IDefault (value, (true, Build_XUBInteger 2))) in
 (uint2N _now > uint2N _cliffEnd) ->
 (uint2N _now < uint2N _vestingEnd) ->
 (isMessageSent mes addr 0 
 (toValue (eval_state (sRReader (ULtoRValue (IDefault_left rec def))) l')) = true)
   -> (uint2N value > 0) /\
   ( uint2N value = (vestingPeriods * uint2N _vestingAmount)).
