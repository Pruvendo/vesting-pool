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
Local Open Scope N_scope.
Local Open Scope string_scope.
Require Import VestingPool.interfaces.IVestingService. (*interface*)
Require Import VestingPool.VestingPool. (*contract*)
(*Require Import VestingPool.Modifiers. (*contract*) *)
Module VestingServiceContract.

Contract VestingService ;
Sends To 
    IVestingService (*interface*) 
    (* VestingPool *)
    ; 
(* Контракты *)
(* Inherits  Modifiers ; *)
Record Contract := {
   emae0 : _static ( cell_);
   emae1 : _static ( cell_);
   m_poolCode :  cell_;
   m_nextId :  uint256
}.

UseLocal  cell_.
UseLocal  builder_.
UseLocal  uint256.
Definition mapping_uint256_uint256 := mapping uint256 uint256 .
UseLocal  mapping_uint256_uint256.
Definition mapping_uint256_boolean := mapping uint256 boolean .
UseLocal mapping_uint256_boolean.


Definition FEE_CLAIM : uint :=  ( (*0.1 ton*) 100000000).
Definition FEE_CREATE : uint := ( (*0.1 ton*) 100000000).
Definition CONSTRUCTOR_GAS : uint := ( (*0.1 ton*) 100000000).
Definition ERR_LOW_FEE := 101.
Definition ERR_INVALID_SENDER := 102.
Definition ERR_EMPTY_CELL := 103.
Definition ERR_ADDR_ZERO := 104.
Definition ERR_LOW_AMOUNT := 105.
Definition ERR_LOW_BALANCE := 106.
Definition ERR_NOT_SELF := 107.


Notation " 'FEE_CLAIM' " := (sInject FEE_CLAIM ) (in custom URValue at level 0) : ursus_scope. 
Notation " 'FEE_CREATE' " := (sInject FEE_CREATE) (in custom URValue at level 0) : ursus_scope.
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

Ursus Definition onCodeUpgrade : internal PhantomType false .
   :://tvm->resetStorage() .
   :://return_ {} |.
Defined. 

Ursus Definition setPoolImage (image :  cell_): public PhantomType false .
(* TODO *)
  (* refine (onlyOwner  _) .
  refine (accept  _) . *)
(* TODO *)
   :://m_poolCode := {} (* #{image}->toSlice()->loadRef() *) .
   :://return_ {} |.
Defined. 

Ursus Definition calcCreateGasFee (count :  uint128): private ( uint128) false .
   :://return_  (( β CONSTRUCTOR_GAS + (#{count} * β FEE_CLAIM)) + β FEE_CREATE) |.
Defined. 

Ursus Definition getCreateFee (claimers :  uint128): external ( uint128) false .
   (* :://{fee} := calcCreateGasFee(#{claimers})  |. *)
   :://return_ calcCreateGasFee(#{claimers})  |.
Defined. 

Ursus Definition getPoolCodeHash : external ( uint256) false .
   ::// new 'b : (  builder_ ) @ "b" ; _ |.
   :://{b}->store(address(this)) .
   (* TODO *)
   ::// new 'code : (  cell_ ) @ "code"  (*:= tvm->setCodeSalt(m_poolCode, !{b}->toCell()) *) ; _ |.
   (* ::// {codeHash} := tvm->hash(!{code})   |. *)
   ::// return_ tvm->hash(!{code}) |.
Defined. 

(* TODO *)
(*
Ursus Definition buildPoolImage (creator :  address) (id :  uint256): private ( cell_) false .
   ::// new 'b : (  builder_ ) @ "b"  ; _ |.
   :://{b}->store(address(this)) .
   (* TODO *)
   ::// new 'code : (  cell_ ) @ "code"  (*:= tvm->setCodeSalt(m_poolCode, !{b}->toCell())*) ; _ |.
(* TODO *)
   (* :://return_ tvm->buildStateInit(!{code},       [$ 
        #{id} ⇒ {VestingPool/VestingPool.VestingPool.ClassTypes.VarInit_ι_id};
        #{creator} ⇒ {VestingPool/VestingPool.VestingPool.ClassTypes.VarInit_ι_creator}
      $], VestingPool)  |. *)
   (* return tvm.buildStateInit({
         code: code,
         varInit: {id: id, creator: creator},
         contr: VestingPool
      }); *)

   ::// return_ !{b}->toCell() |.
Fail Defined. 
*)

(*  mapping(uint256 => bool) claimersMap;
        for(uint256 pubkey: claimers) {
            claimersMap[pubkey] = true;
        }
        new VestingPool{
            value: 0,
            flag: 64,
            bounce: true,
            stateInit: buildPoolImage(msg.sender, m_nextId)
        }(amount, cliffMonths, vestingMonths, recipient, claimersMap);
        m_nextId++; *)
Ursus Definition createPool (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  mapping_uint256_uint256 (*uint256'[]*)): external PhantomType false .

(* TODO *)
  (* 
   refine (contractOnly  _) .
   refine (minValue  _) . *)
  (*  
   contractOnly 
   minValue(amount + calcCreateGasFee(uint128(claimers.length))) *)

  
   ::// new 'claimersMap : (  mapping  ( uint256 )( boolean ) ) @ "claimersMap" ;_|.
   (* for(uint256 pubkey: claimers) { *)
   (* :://{claimersMap}[{pubkey}] := TRUE  |. *)
   (* } *)
   (* :// new  |{ VestingPoolPtr }|  
         with 
      [$ 
        (β #{0}) ⇒ { Messsage_ι_value};
        (β #{64}) ⇒ { Messsage_ι_flags};
        TRUE ⇒ { Messsage_ι_bounce};
        buildPoolImage(msg->sender, m_nextId) ⇒ { stateInit}
      $]
        (#{amount}, #{cliffMonths}, #{vestingMonths}, #{recipient}, !{claimersMap}) . *)
   :://m_nextId ++ .
   :://return_ {} |.
Defined. 

Ursus Definition constructor (poolImage :  cell_): public PhantomType false .
(* TODO *)
  (* refine (onlyOwner  _) .
  refine (accept  _) . *)
   :://m_poolCode := {} (* #{poolImage}->toSlice()->loadRef()*) .
   :://m_nextId := (β #{1}) .
   :://return_ {} |.
Defined. 
EndContract Implements (*интерфейсы*) IVestingService.
End VestingServiceContract.