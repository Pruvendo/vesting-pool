Require Import Coq.Program.Basics. 
Require Import String. 

Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad21Instances.  

Require Import UMLang.UrsusLib. 
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Solidity.tvmFunc. 
Require Import UrsusTVM.Solidity.tvmTypes. 

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Inductive LocalFields00I := | ι000 | ι001 .
Definition LocalState00L := [( XHMap (string*nat) ( XUInteger128)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState00L LocalFields00I . 
Opaque LocalState00LRecord . 
Inductive LocalFields01I := | ι010 | ι011 .
Definition LocalState01L := [( XHMap (string*nat) ( XUInteger32)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState01L LocalFields01I . 
Opaque LocalState01LRecord . 
Inductive LocalFields10I := | ι100 | ι101 .
Definition LocalState10L := [( XHMap (string*nat) ( address)) : Type; ( XHMap string nat ) : Type ] .
GlobalGeneratePruvendoRecord LocalState10L LocalFields10I . 
Opaque LocalState10LRecord . 
(**************** LocalState Tree ***************.
 /\
/\\
**************** LocalState Tree ***************)

Inductive LocalFields0I := | ι00 | ι01 . 
Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
GlobalGeneratePruvendoRecord LocalState0L LocalFields0I . 
Opaque LocalState0LRecord . 

Inductive LocalFieldsI := | ι0 | ι1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState10LRecord ] . 
GlobalGeneratePruvendoRecord LocalStateL LocalFieldsI .
Opaque LocalStateLRecord . 


Transparent

LocalState00LRecord
LocalState01LRecord
LocalState10LRecord

LocalState0LRecord.
Transparent LocalStateLRecord.

(* #[global]Program Instance ledgerClass : LedgerClass XBool LedgerLRecord ContractLRecord 
                                LocalStateLRecord VMStateLRecord MessagesAndEventsLRecord 
                                GlobalParamsLRecord OutgoingMessageParamsLRecord .
Next Obligation.
refine ( VMStateLEmbeddedType VMState_ι_isCommitted ).
Defined.
Next Obligation.
refine ( MessagesAndEventsLEmbeddedType _GlobalParams ) .
Defined.
Next Obligation.
refine ( MessagesAndEventsLEmbeddedType _OutgoingMessageParams ).
Defined.  
Fail Next Obligation. *)

#[local]
Obligation Tactic := idtac.

Notation LocalStateField := (LocalStateField XHMap LocalStateLRecord). 

        #[global, program] Instance LocalStateField00 : LocalStateField ( XUInteger128).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00).
        eapply (LocalState00LEmbeddedType ι001). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι00).
        eapply (LocalState00LEmbeddedType ι000). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField00 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField01 : LocalStateField ( XUInteger32).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01).
        eapply (LocalState01LEmbeddedType ι011). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι0). 
eapply TransEmbedded. eapply (_ ι01).
        eapply (LocalState01LEmbeddedType ι010). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField01 : typeclass_instances. 
        

        #[global, program] Instance LocalStateField10 : LocalStateField ( address).
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 

        eapply (LocalState10LEmbeddedType ι101). 
        Defined.
        Next Obligation. 
        
eapply TransEmbedded. eapply (_ ι1). 

        eapply (LocalState10LEmbeddedType ι100). 
        Defined.
        Fail Next Obligation.
        #[local]
        Remove Hints LocalStateField10 : typeclass_instances. 
        