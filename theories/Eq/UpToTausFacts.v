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
     Eq.UpToTausCore.

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

Inductive eutt_bind_clo (r: itree E R1 -> itree E R2 -> Prop) : itree E R1 -> itree E R2 -> Prop :=
| clo_eutt_bind_ U1 U2 RU t1 t2 k1 k2
      (EQV: @eutt E U1 U2 RU t1 t2)
      (REL: forall v1 v2 (RELv: RU v1 v2), r (k1 v1) (k2 v2))
  : eutt_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors eutt_bind_clo.

Lemma eutt_clo_bind:
  eutt_bind_clo <3= cpn2 (eutt_ RR).
Proof.
Admitted.

Lemma eutt_clo_eq_trans:
  eq_trans_clo <3= cpn2 (@eutt_ E _ _ RR).
Proof.
Admitted.

End EUTT_upto.

Arguments eutt_clo_bind : clear implicits.
Arguments eutt_clo_eq_trans : clear implicits.

Section EUTT_transitivitry.

Lemma eutt_trans {E R1 R2 R3} RR1 RR2 RR t1 t2 t3
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
  - assert (DEC: match ot3 with TauF _ => True | _ => False end \/ match ot3 with TauF _ => False | _ => True end) by (destruct ot3; auto).
    destruct DEC as [DEC | DEC].
    + destruct ot3; simpl in DEC; try contradiction.
      econstructor. gbase. eapply CIH; eauto with paco.
      eapply gcpn2_step with (gf := eutt_ RR2) (x0 := Tau t3) (x1 := Tau t) in INR; eauto with paco.
      eapply eutt_elim_tauL, eutt_elim_tauR.
      eauto.
    + inv INR; simpobs; simpl in DEC; try contradiction. econstructor.
      gunfold EQTAUS. red in EQTAUS.
      move EQTAUS0 before CIH. revert_until EQTAUS0.
      induction EQTAUS0; intros; simpl in DEC; try contradiction.
      * remember (RetF r1) as ot. revert Heqot.
        induction EQTAUS; intros; inv Heqot; eauto with paco.
      * remember (VisF e k1) as ot. revert Heqot.
        induction EQTAUS; intros; dependent destruction Heqot; eauto with paco.
        econstructor. intros.
        gbase. eauto.
      * eapply IHEQTAUS0; eauto.
        eapply gcpn2_step with (gf := eutt_ RR1) (x1 := Tau t1) in EQTAUS; eauto with paco.
        apply eutt_elim_tauR in EQTAUS.
        gunfold EQTAUS. eauto.
  - remember (VisF e k2) as ot.
    move INR before CIH. revert_until INR.
    induction INR; intros; subst; try dependent destruction Heqot; eauto 7.
    econstructor. intros.
    eauto 8 with rclo paco.
  - eauto.
  - remember (TauF t0) as ot.
    move INR before CIH. revert_until INR.
    induction INR; intros; subst; try dependent destruction Heqot; eauto 7.
    + eapply IHINL. gunfold EQTAUS. eauto.
Qed.

Global Instance eutt_cong_gcpn_ {E R1 R2 RR}:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (gcpn2 (@eutt_ E R1 R2 RR) bot2 bot2).
Proof.
  repeat intro. 

  eapply eutt_trans; eauto; cycle 1.
  { intros; subst; eauto. }
  symmetry in H0.
  eapply eutt_trans; eauto.
  intros; subst; eauto.
Qed.

Global Instance eutt_cong_gcpn {E R1 R2 RR}:
  Proper (eutt eq ==> eutt eq ==> iff)
         (gcpn2 (@eutt_ E R1 R2 RR) bot2 bot2).
Proof.
  split; eapply eutt_cong_gcpn_; auto using symmetry.
Qed.

Global Instance Equivalence_eutt {E R} : @Equivalence (itree E R) (eutt eq).
Proof.
  constructor.
  - apply Reflexive_eutt.
  - apply Symmetric_eutt.
  - red. intros.
    eapply eutt_trans; eauto.
    intros; subst; eauto.
Qed.

End EUTT_transitivitry.

Section EUTT_trans_clo.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  
Definition euttL (r rg: itree E R1 -> itree E R2 -> Prop) t1 t2 :=
  gcpn2 (@eutt_ E _ _ RR) r rg t1 t2.
Hint Unfold euttL.

Definition euttH (r rg: itree E R1 -> itree E R2 -> Prop) t1 t2 :=
  forall t1' t2' (EQ1: t1 ≈ t1') (EQ2: t2 ≈ t2'), gcpn2 (@eutt_ E _ _ RR) r rg t1' t2'.
Hint Unfold euttH.

Lemma euttH_impl_euttL r rg t1 t2
      (EQH: euttH r rg t1 t2):
  euttL r rg t1 t2.
Proof. intros. eapply EQH; reflexivity. Qed.

Lemma euttH_trans r rg t1 t2 t1' t2'
      (EQ1: t1 ≈ t1')
      (EQ2: t2 ≈ t2')
      (EQH: euttH r rg t1' t2'):
  euttH r rg t1 t2.
Proof.
  repeat intro. eapply EQH.
  - rewrite <-EQ1; eauto.
  - rewrite <-EQ2; eauto.
Qed.


Inductive eutt_trans_clo (r : itree E R1 -> itree E R2 -> Prop) :
  itree E R1 -> itree E R2 -> Prop :=
| eutt_trans_clo_intro t1 t2 t3 t4
      (EQVl: t1 ≈ t2)
      (EQVr: t4 ≈ t3)
      (RELATED: r t2 t3)
  : eutt_trans_clo r t1 t4
.
Hint Constructors eutt_trans_clo.

Lemma euttH_vis r rg (LEr: r <2= rg) u (e: E u) k1 k2
      (EQH: forall x, euttL (eutt_trans_clo rg) (eutt_trans_clo rg) (k1 x) (k2 x)):
  euttH r rg (Vis e k1) (Vis e k2).
Proof.
  revert_until LEr. gcofix CIH. intros. unfold euttL in *.
  gstep. red.
  gunfold EQ1. red in EQ1. simpl in *. remember (VisF e k1) as ov1.
  hinduction EQ1 before CIH; intros; eauto; dependent destruction Heqov1.
  gunfold EQ2. red in EQ2. simpl in *. remember (VisF e0 k3) as ov2.
  hinduction EQ2 before CIH; intros; eauto; dependent destruction Heqov2.
  econstructor. intros.

  k3 = k0 =clo rg= k4 = k2
  

  

  
Qed.

End EUTT_trans_clo.  








