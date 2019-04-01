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
     Eq.UpToTaus
     Eq.UpToTausCore
     Eq.Untaus.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)


Section EUTT_Lemmas1.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma eutt_elim_tauL (t1: itree E R1) (t2: itree E R2)
    (REL : @eutt E R1 R2 RR (Tau t1) t2) :
  eutt RR t1 t2.
Proof.
  gunfold REL. gstep. red in REL |- *. simpl in *.
  remember (TauF t1) as ott1.
  move REL before RR. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott1; eauto.
  gunfold EQTAUS. eauto.
Qed.

Lemma eutt_elim_tauR (t1: itree E R1) (t2: itree E R2)
    (REL : @eutt E R1 R2 RR t1 (Tau t2)) :
  eutt RR t1 t2.
Proof.
  gunfold REL. gstep. red in REL |- *. simpl in *.
  remember (TauF t2) as ott2.
  move REL before RR. revert_until REL.
  induction REL; intros; subst; try dependent destruction Heqott2; eauto.
  gunfold EQTAUS. eauto.
Qed.

End EUTT_Lemmas1.

Section EUTT_upto.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  
Inductive tausL_clo (r: itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| clo_eutt_taus_left t1 t1' t2
      (UNT: untaus t1 t1')
      (REL: r t1' t2) :
    tausL_clo r t1 t2
.
Hint Constructors tausL_clo.

Lemma eutt_clo_tausL:
  tausL_clo <3= cpn2 (eutt_ RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  red. red in REL. hinduction UNT before RR; intros.
  + eapply euttF_mon; eauto with rclo.
  + subst. eauto.
Qed.

Inductive tausR_clo (r: itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| clo_eutt_taus_right t1 t2 t2'
      (UNT: untaus t2 t2')
      (REL: r t1 t2') :
  tausR_clo r t1 t2
.
Hint Constructors tausR_clo.

Lemma eutt_clo_tausR:
  tausR_clo <3= cpn2 (eutt_ RR).
Proof.
  ucompat. econstructor; [pmonauto|].
  intros. destruct PR.
  red. red in REL. hinduction UNT before RR; intros.
  + eapply euttF_mon; eauto with rclo.
  + subst. eauto.
Qed.

End EUTT_upto.

Arguments eutt_clo_tausL : clear implicits.
Arguments eutt_clo_tausR : clear implicits.

Section EUTT_transitivity.

Context {E : Type -> Type}.

Lemma eutt_trans {R1 R2 R3} RR1 RR2 RR t1 t2 t3
      (INL: @eutt E R1 R2 RR1 t1 t2)
      (INR: @eutt E R2 R3 RR2 t2 t3)
      (RREQ: forall r1 r2 r3, RR1 r1 r2 -> RR2 r2 r3 -> RR r1 r3: Prop) :
  eutt RR t1 t3.
Proof.
  revert_until RR2. gcofix CIH. intros.
  gstep. gunfold INL. gunfold INR. red in INL, INR |- *.
  genobs_clear t3 ot3. revert ot3 INR.
  induction INL; intros; clear t1 t2.
  - remember (RetF r2) as ot. revert Heqot.
    induction INR; intros; inv Heqot; eauto with paco.
  - destruct (notau_dec ot3) as [EQ | EQ].
    + destruct ot3; simpl in EQ; try contradiction.
      econstructor. gbase. eapply CIH; eauto with paco.
      eapply gcpn2_step with (gf := eutt_ RR2) (x0 := Tau t3) (x1 := Tau t) in INR; eauto with paco.
      eapply eutt_elim_tauL, eutt_elim_tauR.
      eauto.
    + inv INR; simpobs; simpl in EQ; try contradiction. econstructor.
      gunfold EQTAUS. red in EQTAUS.
      move EQTAUS0 before CIH. revert_until EQTAUS0.
      induction EQTAUS0; intros; simpl in EQ; try contradiction.
      * remember (RetF r1) as ot. revert Heqot.
        induction EQTAUS; intros; inv Heqot; eauto with paco.
      * remember (VisF e k1) as ot. revert Heqot.
        induction EQTAUS; intros; dependent destruction Heqot; eauto with paco.
        econstructor. intros. right.
        destruct (EUTTK x); try contradiction.
        destruct (EUTTK0 x); try contradiction.
        gbase. eauto.
      * eapply IHEQTAUS0; eauto.
        eapply gcpn2_step with (gf := eutt_ RR1) (x1 := Tau t1) in EQTAUS; eauto with paco.
        apply eutt_elim_tauR in EQTAUS.
        gunfold EQTAUS. eauto.
  - remember (VisF e k2) as ot.
    move INR before CIH. revert_until INR.
    induction INR; intros; subst; try dependent destruction Heqot; eauto 7.
    econstructor. intros.
    edestruct EUTTK, EUTTK0; eauto 8 with rclo paco.
  - eauto.
  - remember (TauF t0) as ot.
    move INR before CIH. revert_until INR.
    induction INR; intros; subst; try dependent destruction Heqot; eauto 7.
    + eapply IHINL. gunfold EQTAUS. eauto.
Qed.

Global Instance eutt_cong_gcpn_ {R1 R2 RR}:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (gcpn2 (@eutt_ E R1 R2 RR) bot2 bot2).
Proof.
  repeat intro. eapply eutt_trans; eauto; cycle 1.
  { intros; subst; eauto. }
  symmetry in H0.
  eapply eutt_trans; eauto.
  intros; subst; eauto.
Qed.

Global Instance eutt_cong_gcpn {R1 R2 RR}:
  Proper (eutt eq ==> eutt eq ==> iff)
         (gcpn2 (@eutt_ E R1 R2 RR) bot2 bot2).
Proof.
  split; eapply eutt_cong_gcpn_; auto using symmetry.
Qed.

End EUTT_transitivity.

Global Instance Equivalence_eutt {E R} : @Equivalence (itree E R) (eutt eq).
Proof.
  constructor.
  - apply Reflexive_eutt.
  - apply Symmetric_eutt.
  - red. intros.
    eapply eutt_trans; eauto.
    intros; subst; eauto.
Qed.

Section EUTT_Lemmas2.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma eutt_unalltaus t1 t1' t2
      (NOT: unalltaus t1 t1')
      (EQ : @eutt E R1 R2 RR t1 t2):
  exists t2', unalltaus t2 t2'.
Proof.
  gunfold EQ. red in EQ. unfold unalltaus in *.
  destruct NOT as [UNT NOT].
  hinduction UNT before RR; intros.
  - hinduction EQ before RR; intros; subst; try inv NOT.
    + exists (Ret r2). split; simpl; eauto.
    + exists (Vis e k2). split; simpl; eauto.
    + edestruct IHEQ; eauto.
      exists x. split; eauto.
  - edestruct IHUNT; eauto.
    subst. eapply gcpn2_unfold with (gf := eutt_ RR); eauto with paco.
    eapply eutt_elim_tauL. gstep. apply EQ.
Qed.      

Lemma eutt_unalltaus_ret {R} v t1 t2
      (EQ: @eutt E R R eq t1 t2)
      (UNAT: unalltaus t1 (Ret v)):
  unalltaus t2 (Ret v).
Proof.
  gunfold EQ. red in EQ.
  (* TODO: generalize [genobs]. *)
  destruct UNAT. genobs t1 ot1. remember (observe (Ret v)) as orv. symmetry in Heqorv.
  hinduction H before R; intros; subst.
  - red. hinduction EQ before R; intros; subst; inv H0; try inv Heqorv; eauto.
    edestruct IHEQ; simpl; eauto.
  - eapply IHuntausF; eauto.
    eapply gcpn2_unfold with (gf:= eutt_ eq); eauto with paco.
    eapply eutt_elim_tauL. gstep. eauto.
Qed.

Lemma eutt_unalltaus_vis {R U} t1 t2 e (k1: U -> _)
      (EQ: @eutt E R R eq t1 t2)
      (UNAT: unalltaus t1 (Vis e k1)):
  exists k2, unalltaus t2 (Vis e k2) /\ forall u, k1 u ≈ k2 u.
Proof.
  gunfold EQ. red in EQ.
  destruct UNAT. genobs t1 ot1. remember (observe (Vis e k1)) as ok. symmetry in Heqok.
  hinduction H before R; intros; subst.
  - hinduction EQ before R; intros; subst; inv H0; try dependent destruction Heqok; eauto.
    + eexists. split; simpl; eauto.
      intros; edestruct EUTTK; eauto; contradiction.
    + edestruct IHEQ as [? []]; simpl; eauto.
      eexists. split; [split; simpl; eauto|]; eauto.
  - eapply IHuntausF; eauto.
    eapply gcpn2_unfold with (gf:= eutt_ eq); eauto with paco.
    eapply eutt_elim_tauL. gstep. eauto.
Qed.

Lemma untaus_eutt {R} {t1 t2: itree E R}
      (UN: untaus t1 t2):
  t1 ≈ t2.
Proof.
  genobs t1 ot1. genobs t2 ot2.
  hinduction UN before R; intros; subst; eauto.
  - apply observing_intros in Heqot2. rewrite Heqot2. reflexivity.
  - rewrite (simpobs Heqot1), tau_eutt. eauto.
Qed.

End EUTT_Lemmas2.
