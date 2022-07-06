
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


From elpi Require Import elpi.


Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Require Import VestingPool.interfaces.IVestingService. (*interface*)
Require Import VestingPool.VestingPool. (*contract*)
Require Import VestingPool.Modifiers. (*contract*)
Require Import VestingPool.VestLib. (*library*)

Module VestingServiceContract.
Contract VestingService ;
Sends To 
    (*VestingPool*) ; 
(* Контракты *)
(* Inherits  Modifiers ; *)
Constants 
Definition (*VestingService*) ERR_INVALID_RECIPIENT : uint256 := Build_XUBInteger 203%N
Definition (*VestingService*) ERR_NO_CLAIMERS : uint256 := Build_XUBInteger 202%N
Definition (*VestingService*) ERR_TOO_MANY_CLAIMERS : uint256 := Build_XUBInteger 201%N

Definition (*VestLib*) MAX_CLAIMERS : uint256 := Build_XUBInteger 10%N
Definition (*VestLib*) STORAGE_FEE : uint128 := Build_XUBInteger 1000000000(*1 ever*)
Definition (*VestLib*) CONSTRUCTOR_GAS : uint128 := Build_XUBInteger 100000000 (*0.1 ever*)
Definition (*VestLib*) FEE_CREATE : uint128 := Build_XUBInteger 100000000 (*0.1 ever*)
Definition (*VestLib*) FEE_CLAIM : uint128 := Build_XUBInteger 100000000 (*0.1 ever*);

Record Contract := {
   botch0 : _static(uint);
   botch1 : _static(uint);
   m_poolCode :  cell_;
   m_nextId :  uint256;
   m_onbounceMap :  XHMap  ( address )( address )
}.

UseLocal Definition _ := [
     XMaybe  ( address );
     address;
     uint32;
     cell_;
     builder_;
     uint256;
     XHMap  ( uint256 )( boolean )
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

Definition ERR_INVALID_RECIPIENT := 203%N.
Definition ERR_NO_CLAIMERS := 202%N.
Definition ERR_TOO_MANY_CLAIMERS := 201%N.
Notation " 'ERR_INVALID_RECIPIENT' " := (sInject ERR_INVALID_RECIPIENT) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_NO_CLAIMERS' " := (sInject ERR_NO_CLAIMERS) (in custom URValue at level 0) : ursus_scope. 
Notation " 'ERR_TOO_MANY_CLAIMERS' " := (sInject ERR_TOO_MANY_CLAIMERS) (in custom URValue at level 0) : ursus_scope. 

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

              
Ursus Definition onPoolActivated : external PhantomType false .
   Check || m_onbounceMap ->fetch(msg->sender)||.
   ::// new 'entry : (  XMaybe  ( address ) ) @ "entry"  := m_onbounceMap ->fetch(msg->sender); _ |.
   ::// if ( !{entry}->hasValue() ) then { {_:UExpression _ false} } .
   (* TODO *)
   (* delete m_onbounceMap[msg.sender]; ??? *)
   ::// m_onbounceMap:= m_onbounceMap ->delete(msg->sender)|.

   ://return_ {} |.
Defined. 

Notation "'new' x ':' ty ':=' r ';' f  " := (DynamicBinding (new_lvalue _)
             (fun x: ULValue ty => StrictBinding (AssignExpression x r) f ) )
              (in custom ULValue at level 0, 
              r custom URValue at level 0,
              ty constr at level 0,       
              f custom ULValue at level 100, (*bug in coq?!*)
              x binder ) : ursus_scope.  

Notation "'new' x ':' ty ';' f  " := (DynamicBinding (new_lvalue _)
             (fun x: ULValue ty => StrictBinding (AssignExpression x || {} || ) f ) )
              (in custom ULValue at level 0, 
              ty constr at level 0,       
              f custom ULValue at level 100, (*bug in coq?!*)
              x binder ) : ursus_scope.


Ursus Definition onBounce (slice :  slice_): external PhantomType true .
   (* TODO *)
   ?::// new 'functionId : (  uint32 ) (* @ "functionId"  :=  #{slice}->decode(uint32) *); _|.
   (* TODO *)
   ::// if ( (!{functionId} == {} (*tvm->functionId(VestingPool)*)) ) then { {_:UExpression _ true} } .
      ::// new 'entry : (  XMaybe  ( address ) ) @ "entry"  := m_onbounceMap->fetch(msg->sender) ;_|.
      ::// if ( !{entry}->hasValue() ) then { {_:UExpression _ true} }  |.
         (* TODO *)
         (* delete m_onbounceMap[msg.sender]; ??? *)
         ::// m_onbounceMap:= m_onbounceMap ->delete(msg->sender).
         ::// new 'poolCreator : (  address ) @ "poolCreator"  := !{entry}->get() ;_|.
         ://tvm->transfer(!{poolCreator}, (β #{0}), FALSE, (β #{64}))  |.

   ://return_ {} |.
Defined. 

Ursus Definition calcPoolConstructorFee (vestingMonths :  uint8): public ( uint128) false .
   :://return_ (((ι (#{vestingMonths}) * FEE_CLAIM) + CONSTRUCTOR_GAS) + STORAGE_FEE) |.
   lia.
Defined. 
Ursus Definition calcCreateGasFee (vestingMonths :  uint8): public ( uint128) false .
   :://return_ (FEE_CREATE + calcPoolConstructorFee(#{vestingMonths})) |.
Defined. 

Ursus Definition getCreateFee (vestingMonths :  uint8): external ( uint128) false .
   ::// return_ calcCreateGasFee(#{vestingMonths})  |.
Defined. 

Ursus Definition getPoolCodeHash : external ( uint256) false .
   ::// new 'b : (  builder_ ) @ "b" ; _ |.
   ::// {b}->store(address(this)) .
   (* TODO *)
   ::// new 'code : (  cell_ ) @ "code" (* := tvm->setCodeSalt(m_poolCode, !{b}->toCell())*) ; _|.
   ::// return_ tvm->hash(!{code})   |.
Defined. 

(* TODO *)
(* Not Yet Implemented: HOAS universe polymorphism    *)
(* Ursus Definition buildPoolImage (creator :  address) (id :  uint256): private ( cell_) false .
   ::// new 'b : (  builder_ ) @ "b"  ;_|.
   ::// {b}->store(address(this)) .
   (* TODO *)
   ::// new 'code : (  cell_ ) @ "code"  := {} (*tvm->setCodeSalt(m_poolCode, !{b}->toCell())*) ; _|.
   
   ::// new 'dataCell : cell @ "dataCell" := 
      tvm->buildDataInit ( [$ 
         (* #{code} ⇒ {DataInitInit_ι_contr}; *)
         {} ⇒ {DataInitInit_ι_contr} ;
         [$ (#{id}) ⇒ {VestingPoolContract.s_id} ; (#{creator}) ⇒ {VestingPoolContract.s_creator} $] 
            ⇒ {DataInitInit_ι_varInit} 
            $] ) ; _ |.
   ::// return_  {} (*tvm->buildStateInit (!code, !dataCell)*)|.
   
    
   
Defined.  *)
(*
   return tvm.buildStateInit({
            code: code,
            varInit: {id: id, creator: creator},
            contr: VestingPool
        }); 
    *)



Definition validRecipient (addr :  address): modifier .
unfold_mod.
   (* TODO *)
   :://require_(( ((#{addr})->value !=  (β (#{0%N}))  ) (*&& (  ( #{addr}->wid) ==  (β (#{0%N})) *)), ERR_INVALID_RECIPIENT) .

  refine u.
Defined. 
Arguments validRecipient _ {_} {_}.

Definition checkMinMaxClaimers (claimers : mapping uint256 uint256): modifier .
unfold_mod.
Check length_.
   :://require_(((#{claimers})->length() > ( #{0})), ERR_NO_CLAIMERS) .
   :://require_(((β ((#{claimers})->length())) <= MAX_CLAIMERS), ERR_TOO_MANY_CLAIMERS) .
  refine u.
Defined. 
Arguments checkMinMaxClaimers _ {_} {_}.





(* 
   mapping(uint256 => bool) claimersMap;
   for(uint256 pubkey: claimers) {
      claimersMap[pubkey] = true;
   }
   address pool = new VestingPool{
      value: 0,
      flag: 64,
      bounce: true,
      stateInit: buildPoolImage(msg.sender, m_nextId)
   }(amount, cliffMonths, vestingMonths, recipient, claimersMap);
   m_nextId++;
   m_onbounceMap[pool] = msg.sender;
         *)

Ursus Definition createPool (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  mapping uint256 uint256): external PhantomType true .
  refine (contractOnly  _) .
  refine (validRecipient recipient _) .
  refine (checkMinMaxClaimers claimers _) .
  (* TODO *)
  (* refine (minValue  _) . *)
  ::// new 'claimersMap : (  mapping  ( uint256 )( boolean ) ) @ "claimersMap" ;_|.
  ::// for ( 'pubkey : #{claimers} ) do { {_:UExpression _ false} } .
  :://  new ( 'key : uint256 , 'value : uint256 ) @ ( "key" , "value" ) := pubkey ; _ |.  
  ::// {claimersMap} := !{claimersMap} ->set (!{value}, TRUE)|.
  (* TODO *)
  (* ::// new 'pool : (  address ) @ "pool"  := new  {_}(*|{ VestingPoolPtr }|*)
         with 
      [$ 
        (β #{0}) ⇒ { Message_ι_value};
        (β #{64}) ⇒ { Message_ι_flag};
        TRUE ⇒ { Message_ι_bounce};
        buildPoolImage(msg->sender, m_nextId) ⇒ {stateInit}
      $]
        (#{amount}, #{cliffMonths}, #{vestingMonths}, #{recipient}, !{claimersMap}) . *)
   ::// m_nextId ++ .
   
   ::// m_onbounceMap:= m_onbounceMap ->set ({}(*!{pool}*), msg->sender).
   ://return_ {} |.
Defined. 

Ursus Definition constructor (poolImage :  cell_): public PhantomType true .
  refine (onlyOwner  _) .
  refine (accept  _) .
  (* TODO *)
   :://m_poolCode := {} (* #{poolImage}->toSlice()->loadRef() *) .
   :://m_nextId := (β #{1}) .
   :://return_ {} |.
Defined. 
EndContract Implements (*интерфейсы*) IVestingService.
End VestingServiceContract.