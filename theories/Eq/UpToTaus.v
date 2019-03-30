(** * Equivalence up to taus *)

(** We consider tau as an "internal step", that should not be
   visible to the outside world, so adding or removing [Tau]
   constructors from an itree should produce an equivalent itree.

   We must be careful because there may be infinite sequences of
   taus (i.e., [spin]). Here we shall only allow inserting finitely
   many taus between any two visible steps ([Ret] or [Vis]), so that
   [spin] is only related to itself. This ensures that equivalence
   up to taus is transitive (and in fact an equivalence relation).
 *)

(** This file contains only the definition of the [eutt] relation.
    Theorems about [eutt] are split in two more modules:

    - [ITree.Eq.UpToTausCore] proves that [eutt] is reflexive, symmetric,
      and that [ITree.Eq.Eq.eq_itree] is a subrelation of [eutt].
      Equations for [ITree.Core.ITreeDefinition] combinators which only rely on
      those properties can also be found here.

    - [ITree.Eq.UpToTausEquivalence] proves that [eutt] is transitive,
      and, more generally, contains theorems for up-to reasoning in
      coinductive proofs.
 *)

(** Splitting things this way makes the library easier to build in parallel.
 *)

(* begin hide *)
Require Import Paco.paco.

From ITree Require Import
     Core.ITreeDefinition.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Section EUTT.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive euttF (euttH eutt: itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop :=
| euttF_ret r1 r2
      (RBASE: RR r1 r2):
    euttF euttH eutt (RetF r1) (RetF r2)
| euttF_tau_tau t1 t2
      (EQTAUS: eutt t1 t2):
    euttF euttH eutt (TauF t1) (TauF t2)
| euttF_vis u (e : E u) k1 k2
      (EUTTK: forall x, euttH (k1 x) (k2 x) \/ eutt (k1 x) (k2 x)):
    euttF euttH eutt (VisF e k1) (VisF e k2)
| euttF_tau_left t1 ot2
      (EQTAUS: euttF euttH eutt (observe t1) ot2):
    euttF euttH eutt (TauF t1) ot2
| euttF_tau_right ot1 t2
      (EQTAUS: euttF euttH eutt ot1 (observe t2)):
    euttF euttH eutt ot1 (TauF t2)
.
Hint Constructors euttF.

Definition eutt_ eutt t1 t2 := euttF bot2 eutt (observe t1) (observe t2).
Hint Unfold eutt_.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)

Definition eutt t1 t2 := gcpn2 eutt_ bot2 bot2 t1 t2.
Hint Unfold eutt.

Lemma euttF_mon r r' s s' x y
    (EUTT: euttF r s x y)
    (LEr: r <2= r')
    (LEs: s <2= s'):
  euttF r' s' x y.
Proof.
  induction EUTT; eauto.
  econstructor; intros. edestruct EUTTK; eauto.
Qed.

Lemma monotone_eutt_ : monotone2 eutt_.
Proof. red; intros. eapply euttF_mon; eauto. Qed.
Hint Resolve monotone_eutt_ : paco.

Lemma eutt_fold :
  eutt <2= gcpn2 eutt_ bot2 bot2.
Proof. intros. apply PR. Qed.
Hint Resolve eutt_fold.

Global Arguments eutt t1%itree t2%itree.

End EUTT.

Hint Constructors euttF.
Hint Unfold eutt_.
Hint Unfold eutt.
Hint Resolve monotone_eutt_ : paco.
Hint Resolve eutt_fold.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.
