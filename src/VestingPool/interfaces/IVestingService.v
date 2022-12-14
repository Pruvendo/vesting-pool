
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

Import UrsusNotations.
Local Open Scope xlist_scope.
Local Open Scope record.
Local Open Scope program_scope.
Local Open Scope glist_scope.
Local Open Scope ursus_scope.
Local Open Scope usolidity_scope.

Interfaces.

MakeInterface Class IVestingService :=
{     
    getPoolCodeHash :  external ( uint256) false;
    getCreateFee : (  uint8 ) -> external ( uint128) false;
    createPool : (  uint128 ) -> (  uint8 ) -> (  uint8 ) -> (  address ) -> ( mapping uint256 uint256 ) -> external PhantomType true
}.
EndInterfaces.
