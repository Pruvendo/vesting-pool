
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
Module VestLib.
Contract VestLib ;
Sends To  ; 
(* Контракты *)
(* Inherits   ; *)
Constants 
Definition (*VestLib*) MAX_CLAIMERS : uint256 := Build_XUBInteger 10%N
Definition (*VestLib*) STORAGE_FEE : uint128 := Build_XUBInteger 1000000000(*1 ever*)
Definition (*VestLib*) CONSTRUCTOR_GAS : uint128 := Build_XUBInteger 100000000 (*0.1 ever*)
Definition (*VestLib*) FEE_CREATE : uint128 := Build_XUBInteger 100000000 (*0.1 ever*)
Definition (*VestLib*) FEE_CLAIM : uint128 := Build_XUBInteger 100000000 (*0.1 ever*);

Record Contract := {
   botch0 : _static(uint);
   botch1 : _static(uint);
}.

UseLocal Definition _ := [
].


Ursus Definition calcPoolConstructorFee (vestingMonths :  uint8): public ( uint128) false .
   :://return_ (((ι (#{vestingMonths}) * FEE_CLAIM) + CONSTRUCTOR_GAS) + STORAGE_FEE) |.
   lia.
Defined. 

Ursus Definition calcCreateGasFee (vestingMonths :  uint8): public ( uint128) false .
   :://return_ (FEE_CREATE + calcPoolConstructorFee(#{vestingMonths})) |.
Defined. 
EndContract Implements (*интерфейсы*) .
End VestLib.