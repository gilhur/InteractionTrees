(** * Simple facts about equivalence up to taus *)

(** This module proves simple facts about the [eutt] relation defined in
    [UpToTaus]. *)

(* begin hide *)
From Coq Require Import
     Program (* [revert_until] *)
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From Paco Require Import paco.

From ITree Require Import
     Core.ITreeDefinition.

From ITree Require Export
     Eq.Eq
     Eq.UpToTaus.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)

Section EUTT_homo.

Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).

Global Instance subrelation_eq_eutt :
  @subrelation (itree E R) (eq_itree RR) (eutt RR).
Proof.
  gcofix CIH; gstep. intros.
  gunfold H0. repeat red in H0 |- *. inv H0; eauto 7 with paco.
Qed.

Global Instance Reflexive_eutt_param `{Reflexive _ RR}
       (r rg: itree E R -> itree E R -> Prop) :
  Reflexive (gcpn2 (eutt_ RR) bot3 r rg).
Proof.
  repeat intro.
  eapply gcpn2_mon with (r:=bot2) (rg:=bot2); eauto with paco; try contradiction.
  revert x. gcofix CIH; gstep. intros. repeat red.
  destruct (observe x); eauto 7 with paco.
Qed.

End EUTT_homo.

Section EUTT_hetero.

Context {E : Type -> Type}.

Lemma Symmetric_euttF_hetero {R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (r1 : _ -> _ -> Prop) (r2 : _ -> _ -> Prop) (r'1 : _ -> _ -> Prop) (r'2 : _ -> _ -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1)
      (SYM_r : forall i j, r1 i j -> r2 j i)
      (SYM_r' : forall i j, r'1 i j -> r'2 j i) :
  forall (ot1 : itree' E R1) (ot2 : itree' E R2),
    euttF RR1 r1 r'1 ot1 ot2 -> euttF RR2 r2 r'2 ot2 ot1.
Proof.
  intros. induction H; eauto 7.
  econstructor; intros. edestruct EUTTK; eauto 7.
Qed.

Lemma Symmetric_eutt_hetero {R1 R2}
      (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R1 -> Prop)
      (SYM_RR : forall r1 r2, RR1 r1 r2 -> RR2 r2 r1) :
  forall (t1 : itree E R1) (t2 : itree E R2),
    eutt RR1 t1 t2 -> eutt RR2 t2 t1.
Proof.
  gcofix CIH; gstep. intros.
  gunfold H0.
  repeat red in H0 |- *.
  induction H0; eauto 7 with paco.
  econstructor; intros.
  edestruct EUTTK as [TMP | TMP]; [eauto 7 with paco|].
  right. gbase. apply CIH. eauto.
Qed.

Lemma eutt_Ret {R1 R2} (RR: R1 -> R2 -> Prop) x y :
  RR x y -> @eutt E R1 R2 RR (Ret x) (Ret y).
Proof.
  intros; gstep. econstructor. eauto.
Qed.

Lemma eutt_Vis {R1 R2 U} RR (e: E U) k k' :
  (forall x: U, @eutt E R1 R2 RR (k x) (k' x)) ->
  eutt RR (Vis e k) (Vis e k').
Proof.
  intros. gstep. econstructor.
  intros. right. apply H.
Qed.

Definition rcomp {R1 R2 R3} (RR1: R1 -> R2 -> Prop) (RR2: R2 -> R3 -> Prop) :=
  fun r1 r3 => exists r2, RR1 r1 r2 /\ RR2 r2 r3.
Hint Unfold rcomp.

End EUTT_hetero.

Section EUTT_eq.

Context {E : Type -> Type} {R : Type}.

Local Notation eutt := (@eutt E R R eq).

Global Instance subrelation_observing_eutt:
  @subrelation (itree E R) (observing eq) eutt.
Proof.
  repeat intro. eapply subrelation_eq_eutt, observing_eq_itree_eq. eauto.
Qed.

Global Instance Reflexive_eutt: Reflexive eutt.
Proof. apply Reflexive_eutt_param; eauto. Qed.

Global Instance Symmetric_eutt: Symmetric eutt.
Proof.
  repeat intro. eapply Symmetric_eutt_hetero, H.
  intros; subst. eauto.
Qed.

Global Instance eutt_cong_go : Proper (going eutt ==> eutt) go.
Proof. intros ? ? []; eauto. Qed.

Global Instance eutt_cong_observe : Proper (eutt ==> going eutt) observe.
Proof.
  constructor. gstep. gunfold H. auto.
Qed.

Global Instance eutt_cong_tauF : Proper (eutt ==> going eutt) (@TauF _ _ _).
Proof.
  constructor. gstep. econstructor. eauto.
Qed.

Global Instance eutt_cong_VisF {u} (e: E u) :
  Proper (pointwise_relation _ eutt ==> going eutt) (VisF e).
Proof.
  constructor. gstep. econstructor.
  intros. specialize (H x0). eauto.
Qed.

End EUTT_eq.

Lemma eutt_tau {E R1 R2} (RR : R1 -> R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) :
  eutt RR t1 t2 -> eutt RR (Tau t1) (Tau t2).
Proof.
  intros. gstep. econstructor. eauto.
Qed.

Lemma eutt_vis {E R1 R2} (RR : R1 -> R2 -> Prop)
      {U} (e : E U) (k1 : U -> itree E R1) (k2 : U -> itree E R2) :
  (forall u, eutt RR (k1 u) (k2 u)) <->
  eutt RR (Vis e k1) (Vis e k2).
Proof.
  split.
  - intros. gstep; econstructor.
    intros x; specialize (H x). eauto.
  - intros H x.
    gunfold H; inversion H; auto_inj_pair2; subst.
    edestruct EUTTK; eauto with paco.
Qed.

Lemma eutt_ret {E R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  @eutt E R1 R2 RR (Ret r1) (Ret r2) <-> RR r1 r2.
Proof.
  split.
  - intros H. gunfold H; inversion H; auto.
  - intros. gstep; econstructor. auto.
Qed.

Global Instance eutt_when {E} (b : bool) :
  Proper (eutt eq ==> eutt eq) (@ITree.when E b).
Proof.
  repeat intro. destruct b; simpl; eauto. reflexivity.
Qed.

Lemma eutt_map_map {E R S T}
      (f : R -> S) (g : S -> T) (t : itree E R) :
  eutt eq (ITree.map g (ITree.map f t))
          (ITree.map (fun x => g (f x)) t).
Proof.
  apply subrelation_eq_eutt, map_map.
Qed.

Lemma tau_eutt {E R} (t: itree E R) : Tau t ≈ t.
Proof.
  gstep. econstructor.
  destruct (observe t); eauto with paco.
  - constructor. apply reflexivity.
  - constructor. intros. right. apply reflexivity.
Qed.
