
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
Definition (*VestingPool*) CONSTRUCTOR_GAS : uint128 := Build_XUBInteger 100000000 (*0.1 ton*)
Definition (*VestingPool*) VESTING_PERIOD : uint32 := Build_XUBInteger (30 * 86400)(*30 days*);

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


(* ******* *)
Definition ERR_LOW_FEE := 101.
Definition ERR_INVALID_SENDER := 102.
Definition ERR_EMPTY_CELL := 103.
Definition ERR_ADDR_ZERO := 104.
Definition ERR_LOW_AMOUNT := 105.
Definition ERR_LOW_BALANCE := 106.
Definition ERR_NOT_SELF := 107.
Notation " 'ERR_LOW_FEE' " := (sInject ERR_LOW_FEE) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_INVALID_SENDER' " := (sInject ERR_INVALID_SENDER) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_EMPTY_CELL' " := (sInject ERR_EMPTY_CELL) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_ADDR_ZERO' " := (sInject ERR_ADDR_ZERO) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_LOW_AMOUNT' " := (sInject ERR_LOW_AMOUNT) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_LOW_BALANCE' " := (sInject ERR_LOW_BALANCE) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_NOT_SELF' " := (sInject ERR_NOT_SELF) (in custom URValue at level 0) : ursus_scope. 


Definition senderIs (expected :  address): modifier .
unfold_mod.
   :://require_((msg->sender == #{expected}),  ERR_INVALID_SENDER) .
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

Definition onlyOwners (keys :  XHMap  ( uint256 )( boolean )): modifier .
unfold_mod.
   :://require_((#{keys})->exists(msg->pubkey()), (#{100})) .
  refine u.
Defined. 
Arguments onlyOwners _ {_} {_}.

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

Ursus Definition get : external ( uint256 #  address #  uint32 #  address #  uint32 #  uint32 #  uint128 #  uint128 #  uint128) false .
   :://  new ( 'unlocked : uint128 , 'nothing : uint32 ) @ ( "unlocked" , "" ) := calcUnlocked( ) ; _ |.  
   ::// return_ [ [ [ [ [ [ [ [ !id , !creator], !m_createdAt], !m_recipient] , !m_cliffEnd] , !m_vestingEnd] , !m_totalAmount] , !m_remainingAmount] , !{unlocked}] |.
Defined. 

Ursus Definition onBounce (slice :  slice_): external PhantomType false .
   :://tvm->transfer(creator, (β #{0}), FALSE, (β #{64})) .
   :://return_ {} |.
Defined. 

Ursus Definition claim (poolId :  uint256): external PhantomType true .
(* TODO *)
  (* refine (onlyOwners m_claimers _) . *)
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

Ursus Definition constructor (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  XHMap  ( uint256 )( boolean )): public PhantomType true .
  refine (contractOnly  _) .
  (* TODO *)
  (* refine (minValue  _) . *)
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
   ://return_ {} |.
Defined. 

EndContract Implements (*интерфейсы*) IVestingPool.
End VestingPoolContract.
Import VestingPoolContract.
Notation " 'new' lm 'with' d '(' amount ',' cliffMonths ',' vestingMonths ',' recipient ',' claimersMap ')' " := 
   (tvm_newContract_right lm d (constructor_right amount cliffMonths vestingMonths recipient claimersMap) )
(in custom URValue at level 0 (* , lm custom ULValue at level 0 *), d custom URValue at level 0 ) : ursus_scope .
Notation " 'new' lm 'with' d '(' amount ',' cliffMonths ',' vestingMonths ',' recipient ',' claimersMap ')' " := 
   (tvm_newContract_left lm d (constructor_right amount cliffMonths vestingMonths recipient claimersMap) )
   (in custom ULValue at level 0 , lm custom ULValue at level 0, d custom URValue at level 0 ) : ursus_scope .
   