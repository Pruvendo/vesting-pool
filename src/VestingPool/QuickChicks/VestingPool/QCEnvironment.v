Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Logic.FunctionalExtensionality.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21.
Require Import FinProof.Common.
Require Import FinProof.StateMonad21.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.Types.IsoTypes.

Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Solidity.stdTypes.

Require Import UrsusTVM.Solidity.tvmTypes.
Require Import UrsusTVM.Solidity.tvmFunc.
Require Import UrsusTVM.Solidity.tvmNotations.
Require Import UrsusTVM.Solidity.tvmCells.

Require Import CommonQCEnvironment.
Require Import LocalState.VestingPool.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".


#[local]
Remove Hints isoid : typeclass_instances. 
#[local]
Remove Hints iso_show : typeclass_instances.
#[local]
Remove Hints iso_shrink : typeclass_instances.
#[local]
Remove Hints iso_genSized : typeclass_instances.

Require Import VestingPool.VestingPool.
Import VestingPoolContract.
(* ContractLRecord *)

#[global] 
Instance Contract_Show: Show ContractLRecord.
refine Showxprod.
Defined.

#[global] 
Instance Contract_Shrink: Shrink ContractLRecord.
refine Shrinkxprod.
Defined.

#[global] 
Instance Contract_GenSized: GenSized ContractLRecord. 
refine GenSizedxprod.
Defined.

(*MessagesAndEvents*)

#[global] 
Instance MessagesAndEvents_Show: Show MessagesAndEventsLRecord.
refine Showxprod.
Defined.

#[global] 
Instance MessagesAndEvents_Shrink: Shrink MessagesAndEventsLRecord.
refine Shrinkxprod.
Defined.

#[global] 
Instance MessagesAndEvents_GenSized: GenSized MessagesAndEventsLRecord. 
refine GenSizedxprod.
Defined.

(*LocalState*)

#[global] 
Instance LocalState_Show: Show LocalStateLRecord.
refine Showxprod.
Defined.

#[global] 
Instance LocalState_Shrink: Shrink LocalStateLRecord.
refine Shrinkxprod.
Defined.

#[global] 
Instance LocalState_GenSized: GenSized LocalStateLRecord. 
refine GenSizedxprod.
Defined.

(*Ledger*)

#[global] 
Instance Ledger_Show: Show (LedgerLRecord LocalStateLRecord) | 0.
refine Showxprod.
Defined.

#[global] 
Instance Ledger_Shrink: Shrink (LedgerLRecord LocalStateLRecord)  | 0.
refine Shrinkxprod.
Defined.

#[global] 
Instance Ledger_GenSized: GenSized (LedgerLRecord LocalStateLRecord) | 0 . 
refine GenSizedxprod.
Defined.

(*****************************************************)


#[global] Instance LedgerEq_Dec: forall (l1 l2: LedgerLRecord LocalStateLRecord), Dec (l1 = l2).
intros.
esplit.
unfold decidable.
repeat decide equality.
Defined.


#[global] Instance ContractEq_Dec: forall (l1 l2: ContractLRecord), Dec (l1 = l2).
intros.
esplit.
unfold decidable.
repeat decide equality.
Defined.