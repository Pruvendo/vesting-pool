(* 
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

Contract Modifiers ;
Sends To  ; 
(* Контракты *)
(* Inherits   ; *)
Constants 
Definition (*Modifiers*) ERR_NOT_SELF : uint256 := Build_XUBInteger 107%N
Definition (*Modifiers*) ERR_LOW_BALANCE : uint256 := Build_XUBInteger 106%N
Definition (*Modifiers*) ERR_LOW_AMOUNT : uint256 := Build_XUBInteger 105%N
Definition (*Modifiers*) ERR_ADDR_ZERO : uint256 := Build_XUBInteger 104%N
Definition (*Modifiers*) ERR_EMPTY_CELL : uint256 := Build_XUBInteger 103%N
Definition (*Modifiers*) ERR_INVALID_SENDER : uint256 := Build_XUBInteger 102%N
Definition (*Modifiers*) ERR_LOW_FEE : uint256 := Build_XUBInteger 101%N;

Record Contract := {
  botch0 : _static(uint);
   botch1 : _static(uint);
}.

UseLocal Definition _ := [
].
(* 

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
Arguments onlyOwner  {_} {_}. *)
EndContract Implements (*интерфейсы*) . *)