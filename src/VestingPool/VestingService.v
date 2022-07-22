
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
Require Import VestingPool.interfaces.IVestingService.
Require Import VestingPool.interfaces.IVestingPool. (*interface*)
Require Import VestingPool.VestingPool. (*contract*)

Require Import VestingPool.Modifiers. (*contract*)
Require Import VestingPool.VestLib. (*library*)




Module VestingServiceContract.
Contract VestingService ;
Sends To 
IVestingPool ; 
(* Контракты *)
(* Inherits  Modifiers ; *)
Constants 
Definition (*VestLib*) MAX_CLAIMERS : uint256 := Build_XUBInteger 10%N
Definition (*VestLib*) STORAGE_FEE : uint128 := Build_XUBInteger 30 (*1 ever*)
Definition (*VestLib*) CONSTRUCTOR_GAS : uint128 := Build_XUBInteger 3 (*0.1 ever*)
Definition (*VestLib*) FEE_CREATE : uint128 := Build_XUBInteger 3 (*0.1 ever*)
Definition (*VestLib*) FEE_CLAIM : uint128 := Build_XUBInteger 3 (*0.1 ever*)
Definition ERR_LOW_FEE :uint := 101
Definition ERR_INVALID_SENDER :uint := 102
Definition ERR_EMPTY_CELL :uint := 103
Definition ERR_ADDR_ZERO :uint := 104
Definition ERR_LOW_AMOUNT :uint := 105
Definition ERR_LOW_BALANCE :uint := 106
Definition ERR_NOT_SELF :uint := 107
Definition ERR_INVALID_RECIPIENT :uint := 203
Definition ERR_NO_CLAIMERS :uint := 202
Definition ERR_TOO_MANY_CLAIMERS :uint := 201
;

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

#[override]
Ursus Definition onPoolActivated : external PhantomType false .
   ::// new 'entry : (  XMaybe  ( address ) ) @ "entry"  := m_onbounceMap ->fetch(msg->sender); _ |.
   ::// if ( !{entry}->hasValue() ) then { {_:UExpression _ false} } .
   (* TODO *)
   (* delete m_onbounceMap[msg.sender]; ??? *)
   ::// m_onbounceMap:= m_onbounceMap ->delete(msg->sender)|.

   ://return_ {} |.
Defined.
Sync. 



Ursus Definition onBounce (slice :  slice_): external PhantomType true .
   (* TODO *)
   ::// new 'functionId : (  uint32 )  @ "functionId" (* :=  #{slice}->decode(uint32) *); _|.
   (* TODO *)
   ::// if ( (!{functionId} == {} (*tvm->functionId(VestingPool)*)) ) then { {_:UExpression _ true} } .
      ::// new 'entry : (  XMaybe  ( address ) ) @ "entry"  := m_onbounceMap->fetch(msg->sender) ;_|.
      ::// if ( !{entry}->hasValue() ) then { {_:UExpression _ true} }  |.
         ::// m_onbounceMap:= m_onbounceMap ->delete(msg->sender).
         ::// new 'poolCreator : (  address ) @ "poolCreator"  := !{entry}->get() ;_|.
         :://tvm->transfer(!{poolCreator}, (β #{0}), FALSE, (β #{64}))  |.

   ://return_ {} |.
Defined.
Sync. 

(* VestLib *)
Ursus Definition calcPoolConstructorFee (vestingMonths :  uint8): public ( uint128) false .
   :://return_ (((ι (#{vestingMonths}) * FEE_CLAIM) + CONSTRUCTOR_GAS) + STORAGE_FEE) |.
   lia.
Defined.
Sync.
(* VestLib *)
Ursus Definition calcCreateGasFee (vestingMonths :  uint8): public ( uint128) false .
   :://return_ (FEE_CREATE + calcPoolConstructorFee(#{vestingMonths})) |.
Defined. 
Sync.

#[override]
Ursus Definition getCreateFee (vestingMonths :  uint8): external ( uint128) false .
   ::// return_ calcCreateGasFee(#{vestingMonths})  |.
Defined.
Sync. 

#[override]
Ursus Definition getPoolCodeHash : external ( uint256) false .
   ::// new 'b : (  builder_ ) @ "b" ; _ |.
   ::// {b}->store(address(this)) .
   (* TODO *)
   ::// new 'code : (  cell_ ) @ "code" (* := tvm->setCodeSalt(m_poolCode, !{b}->toCell())*) ; _|.
   ::// return_ tvm->hash(!{code})   |.
Defined.
Sync. 

(* TODO *)
(* Not Yet Implemented: HOAS universe polymorphism    *)
Set UrsusDefault "Empty".
Ursus Definition buildPoolImage (creator :  address) (id :  uint256): private ( cell_) false .
   ::// new 'b : (  builder_ ) @ "b"  ;_|.
   ::// {b}->store(address(this)) .
   (* TODO *)
   ::// new 'code : (  cell_ ) @ "code"  := {} (*tvm->setCodeSalt(m_poolCode, !{b}->toCell())*) ; _|.
   
   ::// new 'dataCell : cell @ "dataCell" := 
      tvm->buildDataInit ( [$ 
          (#{"VestingPool"}) ⇒ {DataInitInit_ι_contr} ;
         [$ (#{id}) ⇒ {VestingPoolContract.s_id} ; (#{creator}) ⇒ {VestingPoolContract.s_creator} $] 
            ⇒ {DataInitInit_ι_varInit} 
            $] ) ; _ |.
   ::// return_  tvm->buildStateInit (!code, !dataCell)|.
Defined.
Sync. 
Set UrsusDefault "MakeUrsusDefinitions".
(*
   return tvm.buildStateInit({
            code: code,
            varInit: {id: id, creator: creator},
            contr: VestingPool
        }); 
*)

Definition buildPoolImage_right {b0 b1}
(creator: URValue  address  b0 ) 
(id: URValue  uint256  b1 ) : URValue ( cell_ ) (orb b1 b0) :=
wrapURExpression (cell_) (orb (orb false b1 ) b0 ) (_ )
(ursus_call_with_args (orb (orb false b1 ) b0 )
 (address ->  uint256 -> UExpressionP uint optional tuple mapping cell_ false) λ2 buildPoolImage creator id).
Notation " 'buildPoolImage' '(' creator ',' id ')' " := 
(buildPoolImage_right creator id)  
(in custom URValue at level 0 , 
creator custom URValue at level 0, 
id custom URValue at level 0) : ursus_scope.


Definition validRecipient (addr :  address): modifier .
unfold_mod.
   :://require_(( (#{addr})->value !=  (β (#{0%N}))  ) && ( (#{addr})->wid)  == ( #{(0%Z)})  , ERR_INVALID_RECIPIENT ).
  refine u.
Defined. 
Arguments validRecipient _ {_} {_}.

Definition checkMinMaxClaimers (claimers : mapping uint256 uint256): modifier .
unfold_mod.
   :://require_(((#{claimers})->length() > ( #{0})), ERR_NO_CLAIMERS) .
   :://require_(((β ((#{claimers})->length())) <= MAX_CLAIMERS), ERR_TOO_MANY_CLAIMERS) .
  refine u.
Defined. 
Arguments checkMinMaxClaimers _ {_} {_}.

Notation " 'new' lm 'with' d '(' amount ',' cliffMonths ',' vestingMonths ',' recipient ',' claimersMap ')' " := 
   (tvm_newContract_right lm d (IVestingPool_constructor_right amount cliffMonths vestingMonths recipient claimersMap) )
(in custom URValue at level 0 (* , lm custom ULValue at level 0 *), d custom URValue at level 0 ) : ursus_scope .
Notation " 'new' lm 'with' d '(' amount ',' cliffMonths ',' vestingMonths ',' recipient ',' claimersMap ')' " := 
   (tvm_newContract_left lm d (IVestingPool_constructor_right amount cliffMonths vestingMonths recipient claimersMap) )
   (in custom ULValue at level 0 , lm custom ULValue at level 0, d custom URValue at level 0 ) : ursus_scope .
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
(* msg_sender *)
(* msg_value *)
(* address *)
#[override]
Ursus Definition createPool (amount :  uint128) (cliffMonths :  uint8) (vestingMonths :  uint8) (recipient :  address) (claimers :  mapping uint256 uint256): external PhantomType true .
  :: (contractOnly  _) .
  :: (validRecipient recipient _) .
  :: (checkMinMaxClaimers claimers _) .
  (* TODO *)
  refine {{minValue((#{amount} + calcCreateGasFee(#{vestingMonths}))) ; {_} }} .
  ::// new 'claimersMap : (  mapping  ( uint256 )( boolean ) ) @ "claimersMap" ;_|.
  ::// for ( 'pubkey : #{claimers} ) do { {_:UExpression _ false} } .
  :://  new ( 'key : uint256 , 'value : uint256 ) @ ( "key" , "value" ) := pubkey ; _ |.  
  ::// {claimersMap} := !{claimersMap} ->set (!{value}, TRUE)|.
  ::// new 'pool : (  address ) @ "pool"  := new |{ IVestingPoolPtr }|
         with 
      [$ 
        (β #{0}) ⇒ { DeployInit_ι_value};
        (β #{64}) ⇒ { DeployInit_ι_flag};
        TRUE ⇒ { DeployInit_ι_bounce}; 
        buildPoolImage(msg->sender, m_nextId) ⇒ {DeployInit_ι_stateInit}
      $]
        (#{amount}, #{cliffMonths}, #{vestingMonths}, #{recipient}, !{claimersMap}) ; _|.
   ::// m_nextId ++ .
   ::// m_onbounceMap:= m_onbounceMap ->set (!{pool}, msg->sender).
   :://return_ {} |.
Defined.
Sync. 

#[global, program]
Instance VsetingPoolPtr_booleq: XBoolEquable bool IVestingPool.
Next Obligation.
destruct X, X0.
 1, 4, 9: refine true.
 all : refine false.
Defined.

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

Require Import UMLang.UrsusLib.
Require Import UMLang.ExecGenerator.
Require Import UMLang.ExecGen.GenFlags.
Require Import UMLang.ExecGen.ExecGenDefs.
Locate "IVestingPoolPtr".

Ursus Definition constructor (poolImage :  cell_): public PhantomType true .
  :: (onlyOwner  _) .
  :: (accept  _) .
  (* TODO *)
   :://m_poolCode := {} (* #{poolImage}->toSlice()->loadRef() *) .
   :://m_nextId := (β #{1}) .
   :://return_ {} |.
Defined.
Sync.

(**************)
#[override]
Ursus Definition createClaimersMap  (claimers :  mapping uint256 uint256): external (mapping  ( uint256 )( boolean )) false .
  ::// new 'claimersMap : (  mapping  ( uint256 )( boolean ) ) @ "claimersMap" ;_|.
  ::// for ( 'pubkey : #{claimers} ) do { {_:UExpression _ false} } .
  :://  new ( 'key : uint256 , 'value : uint256 ) @ ( "key" , "value" ) := pubkey ; _ |.  
  ::// {claimersMap} := !{claimersMap} ->set (!{value}, TRUE)|.
   :://return_ !{claimersMap} |.
Defined.
Sync. 

Check createClaimersMap.

EndContract Implements (*интерфейсы*) IVestingService.
End VestingServiceContract.