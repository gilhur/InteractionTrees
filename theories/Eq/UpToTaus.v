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

Inductive taus_up (r: itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| taus_up_base t1 t2
               (BASE: r t1 t2):
    taus_up r t1 t2
| taus_up_left t1 t2
               (REL: taus_up r (Tau t1) t2):
    taus_up r t1 t2
| taus_up_right t1 t2
               (REL: taus_up r t1 (Tau t2)):
    taus_up r t1 t2
.
Hint Constructors taus_up.

Inductive euttF (eutt: itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop :=
| euttF_ret r1 r2
      (RBASE: RR r1 r2):
    euttF eutt (RetF r1) (RetF r2)
| euttF_tau_tau t1 t2
      (EQTAUS: eutt t1 t2):
    euttF eutt (TauF t1) (TauF t2)
| euttF_vis u (e : E u) k1 k2
      (EUTTK: forall x, taus_up eutt (k1 x) (k2 x) : Prop):
    euttF eutt (VisF e k1) (VisF e k2)
| euttF_tau_left t1 ot2
      (EQTAUS: euttF eutt (observe t1) ot2):
    euttF eutt (TauF t1) ot2
| euttF_tau_right ot1 t2
      (EQTAUS: euttF eutt ot1 (observe t2)):
    euttF eutt ot1 (TauF t2)
.
Hint Constructors euttF.

Definition eutt_ eutt t1 t2 := euttF eutt (observe t1) (observe t2).
Hint Unfold eutt_.

(* We now take the greatest fixpoint of [eutt_]. *)

(* Equivalence Up To Taus.

   [eutt t1 t2]: [t1] is equivalent to [t2] up to taus. *)

Definition eutt t1 t2 := gcpn2 eutt_ bot2 bot2 t1 t2.
Hint Unfold eutt.

Lemma taus_up_mon r r' x y
      (EUTT: taus_up r x y)
      (LEr: r <2= r'):
  taus_up r' x y.
Proof.
  induction EUTT; eauto.
Qed.

Hint Resolve taus_up_mon : paco.

Lemma euttF_mon r r' x y
      (EUTT: euttF r x y)
      (LEr: r <2= r'):
  euttF r' x y.
Proof.
  induction EUTT; eauto with paco.
Qed.

Hint Resolve euttF_mon : paco.

Lemma monotone_eutt_ : monotone2 eutt_.
Proof. red; intros. eapply euttF_mon; eauto. Qed.
Hint Resolve monotone_eutt_ : paco.

Lemma eutt_fold :
  eutt <2= gcpn2 eutt_ bot2 bot2.
Proof. intros. apply PR. Qed.
Hint Resolve eutt_fold.

Global Arguments eutt t1%itree t2%itree.

End EUTT.

Hint Constructors taus_up.
Hint Constructors euttF.
Hint Unfold eutt_.
Hint Unfold eutt.
Hint Resolve taus_up_mon : paco.
Hint Resolve euttF_mon : paco.
Hint Resolve monotone_eutt_ : paco.
Hint Resolve eutt_fold.

Infix "≈" := (eutt eq) (at level 70) : itree_scope.
