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

Module VestingPoolContract.
Opaque address.
Contract VestingPool ;
Sends To 
    IOnPoolActivated (*interface*)  ; 
(* Контракты *)
(* Inherits  Modifiers ; *)
Constants 
Definition (*VestingPool*) VESTING_PERIOD : uint32 := Build_XUBInteger (30 * 86400)(*30 days*)
Definition (*VestLib*) MAX_CLAIMERS : uint256 := Build_XUBInteger 10%N
Definition (*VestLib*) STORAGE_FEE : uint128 := Build_XUBInteger 1000000000(*1 ever*)
Definition (*VestLib*)(*VestingPool*) CONSTRUCTOR_GAS : uint128 := Build_XUBInteger 100000000 (*0.1 ever*)
Definition (*VestLib*) FEE_CREATE : uint128 := Build_XUBInteger 100000000 (*0.1 ever*)
Definition (*VestLib*) FEE_CLAIM : uint128 := Build_XUBInteger 100000000 (*0.1 ever*)
Definition ERR_LOW_FEE : uint := 101
Definition ERR_INVALID_SENDER : uint := 102
Definition ERR_EMPTY_CELL : uint := 103
Definition ERR_ADDR_ZERO : uint := 104
Definition ERR_LOW_AMOUNT : uint := 105
Definition ERR_LOW_BALANCE : uint := 106
Definition ERR_NOT_SELF : uint := 107
;
Record Contract := {

   id : _static ( uint256);
   creator : _static ( address);
   m_createdAt :  uint32;
   m_cliffEnd :  uint32;
   m_vestingEnd :  uint32;
   m_vestingFrom :  uint32;
   m_totalAmount :  uint128;
   m_remainingAmount :  uint128;
   m_vestingAmount :  uint128;
   m_recipient :  address;
   m_claimers :  XHMap  ( uint256 )( boolean )
}.
Transparent address.
UseLocal Definition _ := [
     uint128;
     uint32;
     address
].

Definition senderIs (expected :  address): modifier .
unfold_mod.
   :://require_((msg->sender == #{expected}),  ERR_INVALID_SENDER) .
  refine u.
Defined. 
Arguments senderIs _ {_} {_}.

(* TODO *)
Ursus Definition minValue (val :  uint128): public PhantomType true .
(* unfold_mod. *)
   :://require_((msg->value >= #{val}), ERR_LOW_FEE) |.
  (* refine u. *)
Defined.
Sync. 
(* Arguments minValue _ {_} {_}. *)

Definition contractOnly : modifier .
unfold_mod.
   :://require_((msg->sender != {} (*address((β #{0}))*))) .
  refine u.
Defined. 
Arguments contractOnly  {_} {_}.

#[local]
Definition modifier_false := forall X b, UExpression X b -> UExpression X b .

Definition accept : modifier_false .
unfold_mod.
   :://tvm->accept() .
  refine u.
Defined. 
Arguments accept  {_} {_}.

(* TODO *)
Ursus Definition onlyOwners (keys :  XHMap  ( uint256 )( boolean )): public PhantomType true .
(* unfold_mod. *)
   :://require_((#{keys})->exists(msg->pubkey()), (#{100})) |.
  (* refine u. *)
Defined.
Sync. 
(* Arguments onlyOwners _ {_} {_}. *)

Definition onlyOwner : modifier .
unfold_mod.
   :://require_((msg->pubkey() == tvm->pubkey()), (#{100})) .
  refine u.
Defined. 
Arguments onlyOwner  {_} {_}.
(* ******* *)

Ursus Definition calcUnlocked : private ( uint128 #  uint32) false .
   ::// new 'unlocked : (  uint128 ) @ "unlocked"  := (β #{0}) ; _|.
   ::// new 'vestingPeriods : (  uint32 ) @ "vestingPeriods"  := (β #{0}) ; _ |.
   ::// new '_now : (  uint32 ) @ "_now"  := (now) ; _ |.
   ::// if ( (!{_now} > m_cliffEnd) ) then { {_:UExpression _ false} } .
   ::// {vestingPeriods} := ((!{_now} - m_vestingFrom) / VESTING_PERIOD) .
   ::// if ( (!{_now} > m_vestingEnd) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } |.
   ::// {unlocked} := m_remainingAmount  |.
   
   ::// {unlocked} := math->min( m_remainingAmount,  (ι !{vestingPeriods} *  m_vestingAmount))  |.
   lia.

   :://return_ [ !{unlocked}, (!{vestingPeriods} * VESTING_PERIOD) ] |.
Defined.
Sync.
#[override]
Ursus Definition get : external ( uint256 #  address #  uint32 #  address #  uint32 #  uint32 #  uint128 #  uint128 #  uint128) false .
   :://  new ( 'unlocked : uint128 , 'nothing : uint32 ) @ ( "unlocked" , "" ) := calcUnlocked( ) ; _ |.  
   ::// return_ [ [ [ [ [ [ [ [ !id , !creator], !m_createdAt], !m_recipient] , !m_cliffEnd] , !m_vestingEnd] , !m_totalAmount] , !m_remainingAmount] , !{unlocked}] |.
Defined.
Sync. 

Ursus Definition onBounce (slice :  slice_): external PhantomType false .
   :://tvm->transfer(creator, (β #{0}), FALSE, (β #{64})) .
   :://return_ {} |.
Defined.
Sync. 

#[override]
Ursus Definition claim (poolId :  uint256): external PhantomType true .
(* TODO *)
  refine {{ onlyOwners (m_claimers) ; {_} }} .
   :://require_(((#{poolId}) == id)) .
   :://  new ( 'unlocked : uint128 , 'unlockedPeriod : uint32 ) @ ( "unlocked" , "unlockedPeriod" ) := calcUnlocked( ) ; _ |.  
   :://require_((!{unlocked} > (β #{0}))) .
   :://tvm->accept() .
   :://m_remainingAmount -= !{unlocked} .
   :://m_vestingFrom += !{unlockedPeriod} .
   :://tvm->transfer(m_recipient, !{unlocked}, TRUE, (β #{2})) .
   ::// if ( (m_remainingAmount == (β #{0})) ) then { {_:UExpression _ false} } .
   :://selfdestruct(creator)  |.

   ://return_ {} |.
Defined.
Sync. 

Require Import UMLang.UrsusLib.
Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Require Import Generator.Generator.

Context {Ledger : Type}.
Print generate_proof_2.

Hint Unfold
  onlyOwners_left
  onlyOwners
  calcUnlocked
  calcUnlocked_right 
   : unfolderDb.

Hint Unfold 
   (* upd_ledger_fields *)
   tvm_transfer_left 
   new_lvalueL
   wrapURValueL
   wrapURExpressionL
   wrapULExpressionL
   ursus_call_with_argsL
   wrapULExpression 
   rvalued_call_with_argsL
   URValueP0_RValuedWithArgsL
   UExpressionP0_LedgerableWithArgsL
   URValueP_Next_URValueDWithArgsL
   UExpressionP_Next_LedgerableWithRArgsL
   UExpressionP_Next_LedgerableWithLArgsL
   sInjectL
   ULtoRValueL
   tvm_transfer
   (* send_internal_message_
   send_internal_message
   send_internal_message_left
   send_internal_message_pre *)
   suicide_left
   suicide
       : unfolderDb.
Print tvm_transfer.
 

Definition claim_exec_P : forall (l : LedgerLRecord) poolId,
  {l' | l' = exec_state (Uinterpreter (claim poolId)) l}.
Proof.
   intros.
   unfold claim.
   autounfold with unfolderDb.
   fold XBool XUInteger XMaybe XList XProd XHMap.
   idtac "Start auto_build_P";
   repeat auto_build_P; idtac "auto_build_P is successful".
Defined.


Definition claim_exec_trm : forall (l : LedgerLRecord) (poolId : uint256), LedgerLRecord.
intros.
let_term_of_2 claim_exec_P (claim_exec_P l poolId).
Defined.
(* Print claim_exec. *)

Definition claim_exec : forall (l : LedgerLRecord) (poolId : uint256), LedgerLRecord.
intros.
flat_term_of_2 claim_exec_trm (claim_exec_trm l poolId).
Defined.

Definition claim_exec_proof : forall (l : LedgerLRecord) (poolId : uint256), 
 claim_exec l poolId =  exec_state (Uinterpreter (claim poolId)) l.
intros.
proof_of_2 claim claim_exec_P (claim_exec_P l poolId).
Defined.
Print claim_exec_proof.
Local Open Scope N_scope.
Print IDefault_left. (* Тут лежат сообщения дефолтные, но это лвалью, поэтому
это ульвэль надо как-то преобразовать в рвэлью *)

(* The remaining amount for 
each successful claim is decreased by the transfer amount to the recipient *)

(* 
∀ params : eval(claim(params)) = ok(Void) ⟶ 
(let exit = exec(claim(params)).out.messages in exit.size > 0 ∧
 exit[0].method = transfer ∧
  exit[0].receiver = params.m_recipient ∧
   exit[0].value = params.m_remainingValue - exec(claim(params)).this.m_remainingValue) *)
Require Import FinProof.CommonInstances.

#[global]
Instance OutgoingMessage_booleq: forall I `{XBoolEquable bool I}, XBoolEquable bool 
         (OutgoingMessage I).
intros.
esplit.
intros.
case_eq X; intros; case_eq X0; intros.
refine (eqb i i0). refine false. refine false.
refine  (eqb i i1 && eqb i0 i2)%bool.
Defined.

Definition isMessageSent {I}`{XBoolEquable bool I} (m: OutgoingMessage I) (a: address) (n: N)
                        (l: XHMap address (XQueue (OutgoingMessage I))) : bool :=
let subm := q2m (hmapFindWithDefault default a l) in               
let maxk : option N := xHMapMaxKey subm in 
match maxk with 
   | None => false
   | Some k => 
      match hmapLookup (k-n) subm with
      | None => false
      | Some m' => eqb m m'
      end
end. 

#[global, program]
Instance IDefault_booleq : XBoolEquable bool IDefault.
Next Obligation.
destruct H2, H3.
refine true.
Defined.

Definition claim_err_P : forall (l : LedgerLRecord) poolId,
  {l' | l' = isError (eval_state (Uinterpreter (claim poolId)) l)}.
Proof.
   intros.
   generate_proof_2 claim.
Defined.


Definition claim_err_P_trm : forall (l : LedgerLRecord) (poolId : uint256), bool.
intros.
let_term_of_2 claim_err_P (claim_err_P l poolId).
Defined.
Print claim_err_P_trm.

Definition claim_err : forall (l : LedgerLRecord) (poolId : uint256), bool.
intros.
flat_term_of_2 claim_err_P_trm (claim_err_P_trm l poolId).
Defined.
Print claim_err.

Lemma claim_err_prf : forall (l : LedgerLRecord) (poolId : uint256), 
    claim_err l poolId = isError (eval_state (Uinterpreter (claim poolId)) l).
Proof.
   intros.
   proof_of_2 claim_err claim_err_P (claim_err_P l poolId).
Qed.

Tactic Notation "noarith" "compute" "-" ident(ln) := (
  compute -[N.add N.ltb N.sub N.leb N.min N.mul N.div ln]
).

Tactic Notation "noarith" "compute" "in" hyp(H) := (
  compute -[N.add N.ltb N.sub N.leb N.min N.mul N.div] in H
).
Require Import ssreflect.
Tactic Notation "generate_exec" := (
  let P := fresh "P" in
  let eq := fresh "eq" in
  match goal with |- ?t = _ => introduce t as P;
  [
    fold XBool XUInteger XMaybe XList XProd XHMap;
    repeat auto_build_P
  | extract_eq_flat of P as eq term L;
    rewrite -eq ; clear eq
  ]
  end).

Lemma claim_errE : forall (l : LedgerLRecord) (poolId : uint256),
   let id_ : uint256 := toValue (eval_state (sRReader || id || ) l) in 
   (eqb poolId id_) = true ->
   toValue (eval_state (sRReader || {URScalar poolId } == id ||) l) = true ->
   claim_err l poolId = false.
Proof.
   intros.
   remember (claim_err l poolId) as er.
   cbv beta delta [claim_err] in Heqer.
   rewrite Heqer.
   rewrite H3. auto.
Qed.

(* Definition claim_exec_proof : forall (l : LedgerLRecord) (poolId : uint256), 
 claim_exec l poolId =  exec_state (Uinterpreter (claim poolId)) l.
intros.
proof_of_2 claim claim_exec_P (claim_exec_P l poolId).
Defined.
Print claim_exec_proof.
Local Open Scope N_scope.
 *)
Check (EmptyMessage IDefault (Build_XUBInteger 0, (false, Build_XUBInteger 64))).
(*Print isMessageSent.
 *)



(* VestLib *)
Ursus Definition calcPoolConstructorFee (vestingMonths :  uint8): public ( uint128) false .
   :://return_ (((ι (#{vestingMonths}) * FEE_CLAIM) + CONSTRUCTOR_GAS) + STORAGE_FEE) |.
   lia.
Defined.
Sync. 


Ursus Definition constructor (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )): public PhantomType true .
  :: (contractOnly  _) .
  (* TODO *)
  refine {{minValue( #{amount} + (* VestLib *)calcPoolConstructorFee(#{vestingMonths}))  ; {_} }} .
  (* TODO *)
   ::// new 'service : (  address ) @ "service"  := {} (*tvm->codeSalt(tvm->code())->get()->toSlice()->decode(address) *); _ |.
   :://require_((!{service} == msg->sender), ERR_INVALID_SENDER) .
   :://m_createdAt := now.
   :://m_cliffEnd := (m_createdAt + (ι (#{cliffMonths}) * (β #{30}))) .
   lia.
   :://m_vestingEnd := (m_cliffEnd + (ι (#{vestingMonths}) * (β #{30}))) .
   lia.
   :://m_totalAmount := #{amount} .
   :://m_remainingAmount := m_totalAmount .
   :://m_recipient := #{recipient} .
   :://m_claimers := #{claimers} .
   :://m_vestingFrom := m_cliffEnd .
   
   :://m_vestingAmount :=  ((#{vestingMonths}) > (β #{0})) ? (m_totalAmount / ι #{vestingMonths}) : m_totalAmount .
   lia.
   (* IOnPoolActivated(service).onPoolActivated{
            value: 0.03 ever, bounce: false, flag: 0
        }(); *)
   
   ::// IOnPoolActivated.onPoolActivated ( ) 
         ⤳ (!{service}) with 
         [$ 
               (β #{30000000} (*0.03 ever*)) ⇒ { Message_ι_value};
               FALSE ⇒ { Message_ι_bounce};
               (β #{0}) ⇒ { Message_ι_flag}
         $].
   :://return_ {} |.
Defined.
Sync. 

(*The value of pool creation must cover the vesting amount as well as following fee : for pool creation, for each claim, for storage*)
Axiom GVS_06 : forall l l' (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )),
uint2N (toValue (eval_state (sRReader || msg->value  || ) l')) > 
uint2N  amount  + 
 uint2N (toValue (eval_state (sRReader || CONSTRUCTOR_GAS  || ) l')) + 
 uint2N (toValue (eval_state (sRReader || STORAGE_FEE  || ) l')) + 
uint2N (toValue (eval_state (sRReader || FEE_CLAIM  || ) l')) * uint2N vestingMonths  -> 
isError (eval_state (Uinterpreter (constructor amount cliffMonths vestingMonths recipient claimers)) l) = true.


 (*A list of clients can not be updated after the pool is created*)
 Axiom GVS_09 : forall l l' _claimers _claimers' (poolId : uint256),
 l' = exec_state (Uinterpreter (claim poolId)) l ->
 _claimers = toValue (eval_state (sRReader || m_claimers || ) l) ->
 _claimers' = toValue (eval_state (sRReader || m_claimers || ) l') ->
 _claimers = _claimers'.
 (*A  receiver of funds can not be updated after the pool is created.*)
 Axiom GVS_10 : forall l l' _recipient _recipient' (poolId : uint256),
 l' = exec_state (Uinterpreter (claim poolId)) l ->
 _recipient = toValue (eval_state (sRReader || m_recipient || ) l) ->
 _recipient' = toValue (eval_state (sRReader || m_recipient || ) l') ->
 _recipient = _recipient'.
(*Vesting pool parameters must be initialized by the constructor*)
Axiom GVS_11 : forall l l' (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )),
isError (eval_state (Uinterpreter (constructor amount cliffMonths vestingMonths recipient claimers)) l) = false ->
l' = exec_state (Uinterpreter (constructor amount cliffMonths vestingMonths recipient claimers)) l ->
(* m_createdAt = params.now *)
toValue (eval_state (sRReader || m_createdAt || ) l') = toValue (eval_state (sRReader || (now) || ) l) /\
(* m_recipient = params.recipient *)
toValue (eval_state (sRReader || m_recipient || ) l') = recipient /\
(* m_claimers = claimers *)
toValue (eval_state (sRReader || m_claimers || ) l') = claimers /\
(* m_cliffEnd = params.now + params.cliffMonths * 30 * 86400 *)
uint2N (toValue (eval_state (sRReader || m_cliffEnd || ) l')) = uint2N (toValue (eval_state (sRReader || (now) || ) l)) + uint2N (cliffMonths)*30*86400 /\
(* m_vestingEnd = params.now + (params.cliffMonths + params.vestingMonths) * 30 * 86400 *)
uint2N (toValue (eval_state (sRReader || m_vestingEnd || ) l')) = uint2N (toValue (eval_state (sRReader || (now) || ) l)) + uint2N (vestingMonths)*30*86400 /\
(* m_totalAmount = params.amount *)
toValue (eval_state (sRReader || m_totalAmount || ) l') = amount /\
(* m_remainingAmount = params.amount *)
toValue (eval_state (sRReader || m_remainingAmount || ) l') = amount.
(*Funds are locked in the pool to return until the deadline of the open window.*)
Axiom GVS_12_1 : forall l l' (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )),
isError (eval_state (Uinterpreter (constructor amount cliffMonths vestingMonths recipient claimers)) l) = false ->
l' = exec_state (Uinterpreter (constructor amount cliffMonths vestingMonths recipient claimers)) l ->
uint2N (toValue (eval_state (sRReader || tvm->balance () || ) l')) > uint2N amount.
Axiom GVS_12_2 : forall l l'  (poolId : uint256),
l' = exec_state (Uinterpreter (claim poolId)) l ->
uint2N (toValue (eval_state (sRReader || tvm->balance () || ) l)) > uint2N (toValue (eval_state (sRReader || m_remainingAmount || ) l)) ->
uint2N (toValue (eval_state (sRReader || tvm->balance () || ) l')) > uint2N (toValue (eval_state (sRReader || m_remainingAmount || ) l')).

(*To prevent incorrect usage of the pool it can  transfer only once per time-slot after the first call. The  rest of calls to transfer within a time are rejected.  *)
(* TODO l' = l' with now' *)
Axiom GVS_13 : forall l l' _now _now' _VESTING_PERIOD _vestingFrom n (poolId : uint256),
l' = exec_state (Uinterpreter (claim poolId)) l ->
isError (eval_state (Uinterpreter (claim poolId)) l) = false ->
_now = toValue (eval_state (sRReader || (now) || ) l) ->
_now' = toValue (eval_state (sRReader || (now) || ) l') ->
_VESTING_PERIOD = toValue (eval_state (sRReader || VESTING_PERIOD || ) l) ->
_vestingFrom = toValue (eval_state (sRReader || m_vestingFrom || ) l) ->
(uint2N _now > uint2N _vestingFrom + n* uint2N _VESTING_PERIOD) ->
(uint2N _now < uint2N _vestingFrom + (n+1)* uint2N _VESTING_PERIOD) ->
(uint2N _now' > uint2N _vestingFrom + n* uint2N _VESTING_PERIOD) ->
(uint2N _now' < uint2N _vestingFrom + (n+1)* uint2N _VESTING_PERIOD) ->
(uint2N _now <= uint2N _now') ->
isError (eval_state (Uinterpreter (claim poolId)) l') = true.

(*Only claimers can claim *) 
Axiom GVS_14 : forall l _msgSender _claimers (poolId : uint256),
_msgSender = toValue (eval_state (sRReader || msg->pubkey() || ) l)  ->
_claimers = toValue (eval_state (sRReader || m_claimers || ) l)  ->
 _claimers[_msgSender] = false ->
isError (eval_state (Uinterpreter (claim poolId)) l) = true.
(* Any attempts to claim during the cliff period must lead to exception *)
Axiom GVS_15 : forall l _now _cliffEnd (poolId : uint256),
_now = toValue (eval_state (sRReader || (now) || ) l) ->
_cliffEnd = toValue (eval_state (sRReader || m_cliffEnd || ) l) ->
(uint2N _now < uint2N _cliffEnd) ->
isError (eval_state (Uinterpreter (claim poolId)) l) = true. 
(*Any attempt to claim after vestingEnd must lead to sending the rest of the amount to the recipient and the change back to the creator. Also the pool must suicide itself.*)
(* TODO suicide
transfer to creator *)
Axiom GVS_16 : forall l l' addr value _vestingEnd _now (poolId : uint256), 
 false = isError (eval_state (Uinterpreter (claim poolId)) l) -> 
 l' = exec_state (Uinterpreter (claim poolId)) l ->
 _now = toValue (eval_state (sRReader || (now) || ) l) ->
 _vestingEnd = toValue (eval_state (sRReader || m_vestingEnd || ) l) ->
 (uint2N _now > uint2N _vestingEnd) ->
 addr = toValue (eval_state (sRReader || m_recipient || ) l) ->
 value = (toValue (eval_state (sRReader || m_remainingAmount  || ) l)) ->

 let mes := (EmptyMessage IDefault (value, (true, Build_XUBInteger 2))) in
   isMessageSent mes addr 0 
   (toValue (eval_state (sRReader (ULtoRValue IDefault_left)) l')) = true.

 (* The remaining amount for each successful claim is decreased by the transfer amount to the recipient*)
Axiom GVS_17_1 : forall l l' addr value (poolId : uint256), 
 false = isError (eval_state (Uinterpreter (claim poolId)) l) -> 
 l' = exec_state (Uinterpreter (claim poolId)) l ->
 addr = toValue (eval_state (sRReader || m_recipient || ) l) ->
 value = fst (toValue (eval_state (sRReader || calcUnlocked ( ) || ) l)) ->
 let mes := (EmptyMessage IDefault (value, (true, Build_XUBInteger 2))) in
   isMessageSent mes addr 0 
   (toValue (eval_state (sRReader (ULtoRValue IDefault_left)) l')) = true.
(* If the current time is after cliff period and before the vesting end (that effectively means that vesting period is more than zero) the amount to vest is calculated by the following formula*)
Axiom GVS_18 : forall l l' addr value _now _cliffEnd _vestingEnd vestingPeriods _vestingAmount _VESTING_PERIOD _vestingFrom (poolId : uint256), 
(* l = exec_state (Uinterpreter (constructor _ _ _ _)) l_default -> *)
 l' = exec_state (Uinterpreter (claim poolId)) l ->
 addr = toValue (eval_state (sRReader || m_recipient || ) l) ->
 _now = toValue (eval_state (sRReader || (now) || ) l) ->
 _cliffEnd = toValue (eval_state (sRReader || m_cliffEnd || ) l) ->
 _vestingEnd = toValue (eval_state (sRReader || m_vestingEnd || ) l) ->
 (uint2N _now > uint2N _cliffEnd) ->
 (uint2N _now < uint2N _vestingEnd) ->
 _vestingAmount = toValue (eval_state (sRReader || m_vestingAmount || ) l) ->
 _vestingFrom = toValue (eval_state (sRReader || m_vestingFrom || ) l) ->
 _VESTING_PERIOD = toValue (eval_state (sRReader || VESTING_PERIOD || ) l) ->
 vestingPeriods =  (( uint2N _now -  uint2N _vestingFrom) / uint2N _VESTING_PERIOD ) ->
 let mes := (EmptyMessage IDefault (value, (true, Build_XUBInteger 2))) in
 (isMessageSent mes addr 0 
 (toValue (eval_state (sRReader (ULtoRValue IDefault_left)) l')) = true)
   -> (uint2N value > 0) /\
   ( uint2N value = (vestingPeriods * uint2N _vestingAmount)).


EndContract Implements (*интерфейсы*) IVestingPool.
End VestingPoolContract.