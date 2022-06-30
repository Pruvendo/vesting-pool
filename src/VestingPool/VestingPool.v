Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Setoid. 
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Lia.

Require Import FinProof.All.
Require Import UMLang.All.
Require Import UrsusStdLib.Solidity.All.
Require Import UrsusTVM.Solidity.All.


Require Import UrsusDefinitions.
Require Import ForReverseTranslation.
Import UrsusNotations.
Local Open Scope xlist_scope.
Local Open Scope record.
Local Open Scope program_scope.
Local Open Scope glist_scope.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.
Local Open Scope string_scope.
Local Open Scope N_scope.
(*Require Import VestingPool.Modifiers. (*contract*) *)
Require Import VestingPool.interfaces.IVestingPool. (*interface*)
Require Import VestingPool.interfaces.IdbgPool. (*interface*)
Module VestingPoolContract.
   

Contract VestingPool ;
Sends To 
    IVestingPool (*interface*) 
    IdbgPool (*interface*)  ; 
(* Inherits  Modifiers ; *)
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
   m_claimers :  mapping ( uint256 )( boolean );
   m_dbgUnlockAll :  boolean
}.
UseLocal  uint128.
UseLocal  uint32.
UseLocal  address.
UseLocal  uint256.

(* 
Context {VestingPool_ι_CONSTRUCTOR_GAS_  :  uint128 }. 
Notation " 'CONSTRUCTOR_GAS' " := (sInject VestingPool_ι_CONSTRUCTOR_GAS_) (in custom URValue at level 0) : ursus_scope. 
Context {VestingPool_ι_VESTING_PERIOD_  :  uint32 }. 
Notation " 'VESTING_PERIOD' " := (sInject VestingPool_ι_VESTING_PERIOD_) (in custom URValue at level 0) : ursus_scope. 

Context {Modifiers_ι_ERR_NOT_SELF_  :  uint256 }. 
Notation " 'Modifiers->ERR_NOT_SELF' " := (sInject Modifiers_ι_ERR_NOT_SELF_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_LOW_BALANCE_  :  uint256 }. 
Notation " 'Modifiers->ERR_LOW_BALANCE' " := (sInject Modifiers_ι_ERR_LOW_BALANCE_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_LOW_AMOUNT_  :  uint256 }. 
Notation " 'Modifiers->ERR_LOW_AMOUNT' " := (sInject Modifiers_ι_ERR_LOW_AMOUNT_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_ADDR_ZERO_  :  uint256 }. 
Notation " 'Modifiers->ERR_ADDR_ZERO' " := (sInject Modifiers_ι_ERR_ADDR_ZERO_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_EMPTY_CELL_  :  uint256 }. 
Notation " 'Modifiers->ERR_EMPTY_CELL' " := (sInject Modifiers_ι_ERR_EMPTY_CELL_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_INVALID_SENDER_  :  uint256 }. 
Notation " 'Modifiers->ERR_INVALID_SENDER' " := (sInject Modifiers_ι_ERR_INVALID_SENDER_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_LOW_FEE_  :  uint256 }. 
Notation " 'Modifiers->ERR_LOW_FEE' " := (sInject Modifiers_ι_ERR_LOW_FEE_) (in custom URValue at level 0) : ursus_scope.  *)

(* 

Context {Modifiers_ι_ERR_NOT_SELF_  :  uint256 }. 
Notation " 'ERR_NOT_SELF' " := (sInject Modifiers_ι_ERR_NOT_SELF_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_LOW_BALANCE_  :  uint256 }. 
Notation " 'ERR_LOW_BALANCE' " := (sInject Modifiers_ι_ERR_LOW_BALANCE_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_LOW_AMOUNT_  :  uint256 }. 
Notation " 'ERR_LOW_AMOUNT' " := (sInject Modifiers_ι_ERR_LOW_AMOUNT_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_ADDR_ZERO_  :  uint256 }. 
Notation " 'ERR_ADDR_ZERO' " := (sInject Modifiers_ι_ERR_ADDR_ZERO_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_EMPTY_CELL_  :  uint256 }. 
Notation " 'ERR_EMPTY_CELL' " := (sInject Modifiers_ι_ERR_EMPTY_CELL_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_INVALID_SENDER_  :  uint256 }. 
Notation " 'ERR_INVALID_SENDER' " := (sInject Modifiers_ι_ERR_INVALID_SENDER_) (in custom URValue at level 0) : ursus_scope. 
Context {Modifiers_ι_ERR_LOW_FEE_  :  uint256 }. 
Notation " 'ERR_LOW_FEE' " := (sInject Modifiers_ι_ERR_LOW_FEE_) (in custom URValue at level 0) : ursus_scope.  *)


Definition ERR_LOW_FEE := 101.
Definition ERR_INVALID_SENDER := 102.
Definition ERR_EMPTY_CELL := 103.
Definition ERR_ADDR_ZERO := 104.
Definition ERR_LOW_AMOUNT := 105.
Definition ERR_LOW_BALANCE := 106.
Definition ERR_NOT_SELF := 107.
Print XUInteger.
Check Build_XUBInteger.
Definition VESTING_PERIOD : uint :=  (30 (*days*) * 86400).
Definition CONSTRUCTOR_GAS : uint := ( (*0.1 ton*) 100000000).

Notation " 'VESTING_PERIOD' " := (sInject VESTING_PERIOD ) (in custom URValue at level 0) : ursus_scope. 
Notation " 'CONSTRUCTOR_GAS' " := (sInject CONSTRUCTOR_GAS) (in custom URValue at level 0) : ursus_scope. 


Notation " 'ERR_LOW_FEE' " := (sInject ERR_LOW_FEE) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_INVALID_SENDER' " := (sInject ERR_INVALID_SENDER) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_EMPTY_CELL' " := (sInject ERR_EMPTY_CELL) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_ADDR_ZERO' " := (sInject ERR_ADDR_ZERO) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_LOW_AMOUNT' " := (sInject ERR_LOW_AMOUNT) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_LOW_BALANCE' " := (sInject ERR_LOW_BALANCE) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_NOT_SELF' " := (sInject ERR_NOT_SELF) (in custom URValue at level 0) : ursus_scope. 

Definition senderIs (expected :  address): modifier .
unfold_mod.
   ::// require_((msg->sender == #{expected}), ERR_INVALID_SENDER) .
  refine u.
Defined. 
Arguments senderIs _ {_} {_}.

Definition minValue (val :  uint128): modifier .
unfold_mod.
   :://require_((msg->value >= #{val}), ERR_LOW_FEE) .
  refine u.
Defined. 
Arguments minValue _ {_} {_}.

Definition contractOnly : modifier .
unfold_mod.
(* TODO *)
   :://require_((msg->sender != {} (*address((β #{0}))*))) .
  refine u.
Defined. 
Arguments contractOnly  {_} {_}.

#[local]
Definition modifier_false := forall X b, UExpression X b -> UExpression X b .
#[local]
Tactic Notation "unfold_mod_false" := (unfold modifier_false; intros X b u).
Definition accept : modifier_false .
unfold_mod_false.
   :://tvm->accept() .
  refine u.
Defined. 
Arguments accept  {_} {_}.

Definition onlyOwners (keys :  mapping  ( uint256 )( boolean )): modifier .
unfold_mod.
   :://require_(#{keys}->exists(msg->pubkey()), #{100%N} ) .
  refine u.
Defined. 
Arguments onlyOwners _ {_} {_}.

Definition onlyOwner : modifier .
unfold_mod.
   :://require_((msg->pubkey() == tvm->pubkey()), #{100%N}) .
  refine u.
Defined. 
Arguments onlyOwner  {_} {_}.

Ursus Definition unlock : public PhantomType false .
(* TODO *)
  (* refine (senderIs creator _) . *)
  (* senderIs(creator) *)

   :://m_dbgUnlockAll := TRUE .
   :://return_ {} |.
Defined. 

(* Definition shortIfElse{b0 R1 b1} (condition: URValue boolean b0) (thenExpr: UExpression R1 b1).
if ( (!{_now} > m_vestingEnd) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} } . *)
Ursus Definition calcUnlocked : private ( uint128 #  uint32) false .
   ::// new 'unlocked : uint128 @ "unlocked"  := (β #{0}) ; _ |.
   ::// new 'vestingPeriods : (  uint32 ) @ "vestingPeriods"  := (β #{0}) ; _ |.
   ::// new '_now : (  uint32 ) @ "_now"  := ?? m_dbgUnlockAll -> (m_vestingEnd + (β #{1})) -> (now)   ; _ |.
   ::// if ( (!{_now} > m_cliffEnd) ) then { {_:UExpression _ false} } .
   ::// {vestingPeriods} := ((!{_now} - m_vestingFrom) / (β VESTING_PERIOD)) .
   ::// if ( (!{_now} > m_vestingEnd) ) then { {_:UExpression _ false} } else { {_:UExpression _ false} }  |.
   ::// {unlocked} := m_remainingAmount  |.
   ::// {unlocked} := (m_remainingAmount - math->min(m_remainingAmount, (ι !{vestingPeriods} *  ( m_vestingAmount))))  |.
   lia.
   :://return_ [ !{unlocked}, (!{vestingPeriods} * β VESTING_PERIOD) ] |.
Defined. 

Ursus Definition get : external ( uint256 #  address #  uint32 #  address #  uint32 #  uint32 #  uint128 #  uint128 #  uint128) false .
   :://  new ( 'unlocked : uint128 , 'nothing : uint32 ) @ ( "unlocked" , "" ) := calcUnlocked( ) ; _ |.  
   ::// return_ [ [ [ [ [ [ [ [ !id , !creator], !m_createdAt], !m_recipient] , !m_cliffEnd] , !m_vestingEnd] , !m_totalAmount] , !m_remainingAmount] , !{unlocked}] |.
Defined. 

Ursus Definition claim (poolId :  uint256): external PhantomType true .
(* TODO *)
  (* refine (onlyOwners m_claimers _) . *)
  (* onlyOwners(m_claimers) *)

   :://require_((#{poolId} == id)) .
   :://  new ( 'unlocked : uint128 , 'unlockedPeriod : uint32 ) @ ( "unlocked" , "unlockedPeriod" ) := calcUnlocked( ) ; _ |.  
   :://require_((!{unlocked} > (β #{0}))) .
   :://tvm->accept() .
   :://m_remainingAmount -= !{unlocked} .
   :://m_vestingFrom += !{unlockedPeriod} .
   :://tvm->transfer(m_recipient, !{unlocked}, FALSE, (β #{2})) .
   ::// if ( (m_remainingAmount == (β #{0})) ) then { {_:UExpression _ false} } .
   :://selfdestruct(creator)  |.
   :://return_ {} |.
Defined. 

Ursus Definition constructor (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  mapping  ( uint256 )( boolean )): public PhantomType true .
(* TODO *)
  (* refine (contractOnly  _) . *)
  (* refine (minValue  _) . *)
  (* contractOnly 
  minValue(amount + CONSTRUCTOR_GAS) *)
  (* TODO *)
   ::// new 'service : (  address ) @ "service"  :=  {} (*tvm->codeSalt(tvm->code())->get()->toSlice()->decode(address)*) ; _ |.
   ::// require_((!{service} == msg->sender), ERR_INVALID_SENDER) .
   ::// m_createdAt := (now) .
   ::// m_cliffEnd :=  (m_createdAt + ι ( #{cliffMonths} * (β #{30}))) .
   lia.
   ::// m_vestingEnd := (m_cliffEnd + ι (#{vestingMonths} * (β #{30}))) .
   lia.
   :://m_totalAmount := #{amount} .
   :://m_remainingAmount := m_totalAmount .
   :://m_recipient := #{recipient} .
   :://m_claimers := #{claimers} .
   :://m_vestingFrom := m_cliffEnd .
   
   :://m_vestingAmount := ?? ( ( #{vestingMonths}) >  (β #{0})) ->  ( ( m_totalAmount) / ι #{vestingMonths}) -> ( β #{0}).
   lia.
   :://return_ {} |.
Defined. 
EndContract Implements (*интерфейсы*) IVestingPool.
End VestingPoolContract.