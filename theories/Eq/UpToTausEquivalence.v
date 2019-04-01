(* begin hide *)
From Coq Require Import
     Program
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations
     Classical. 

From Paco Require Import paco.

From ITree Require Import
     Basics.CategoryOps
     Basics.Function
     Core.ITreeDefinition.

From ITree Require Export
     Eq.Eq
     Eq.UpToTausCore
     Eq.UpToTausFacts
     Eq.Untaus.

Import ITreeNotations.
Local Open Scope itree.
(* end hide *)


Section EUTT_REL.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Definition eutt_rel := (itree E R1 * itree E R2) + (itree E R1 * itree E R2) -> Prop.

Definition rpair (r1 r2: itree E R1 -> itree E R2 -> Prop) : eutt_rel := fun x =>
  match x with
  | inl (t1,t2) => r1 t1 t2
  | inr (t1,t2) => r2 t1 t2
  end.
Definition rfst (r: eutt_rel) t1 t2 := r (inl (t1,t2)).
Definition rsnd (r: eutt_rel) t1 t2 := r (inr (t1,t2)).
Hint Unfold rpair rfst rsnd.

Lemma rfst_mon r r' t1 t2
      (IN: rfst r t1 t2)
      (LE: r <1= r'):
  rfst r' t1 t2.
Proof. apply LE, IN. Qed.

Lemma rsnd_mon r r' t1 t2
      (IN: rsnd r t1 t2)
      (LE: r <1= r'):
  rsnd r' t1 t2.
Proof. apply LE, IN. Qed.

Lemma rpair_mon r s r' s' p
      (IN: rpair r s p)
      (LEr: r <2= r')
      (LEs: s <2= s'):
  rpair r' s' p.
Proof.
  destruct p, p; eauto.
Qed.

Lemma rpair_bot: rpair bot2 bot2 <1= bot1.
Proof.
  intros. destruct x0, p; contradiction.
Qed.

Hint Resolve rfst_mon rsnd_mon : paco.

End EUTT_REL.

Hint Unfold rpair rfst rsnd.
Hint Resolve rfst_mon rsnd_mon rpair_mon : paco.

Section EUTTG.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Inductive euttHF (euttH euttL: itree E R1 -> itree E R2 -> Prop) : itree' E R1 -> itree' E R2 -> Prop :=
| euttHF_lower ot1 ot2 t1' t2'
      (EQ1: go ot1 ≈ t1')
      (EQ2: go ot2 ≈ t2')
      (RBASE: euttL t1' t2') :
    euttHF euttH euttL ot1 ot2
.
Hint Constructors euttHF.

Definition euttG_ (eutt: eutt_rel) : eutt_rel :=
  rpair (fun t1 t2 => euttHF (rfst eutt) (rsnd eutt) (observe t1) (observe t2))
        (fun t1 t2 => euttF RR (rfst eutt) (rsnd eutt) (observe t1) (observe t2)).
Hint Unfold euttG_.

Definition euttG hr hrg : eutt_rel := gcpn1 euttG_ hr hrg.
Definition euttH h hg r rg t1 t2 := euttG (rpair h r) (rpair hg rg) (inl (t1, t2)).
Definition euttL h hg r rg t1 t2 := euttG (rpair h r) (rpair hg rg) (inr (t1, t2)).

Lemma euttHF_mon h h' r r' x y
    (EUTT: euttHF h r x y)
    (LEh: h <2= h')
    (LEr: r <2= r'):
  euttHF h' r' x y.
Proof.
  destruct EUTT; eauto.
Qed.

Lemma monotone_euttG_ : monotone1 euttG_.
Proof.
  repeat intro.
  destruct x0, p; simpl in *.
  - eapply euttHF_mon; eauto.
  - eapply euttF_mon; eauto.
Qed.
Hint Resolve monotone_euttG_ : paco.

Lemma euttHF_eq_euttG_ r t1 t2:
  euttHF (rfst r) (rsnd r) (observe t1) (observe t2) <-> euttG_ r (inl (t1,t2)).
Proof. reflexivity. Qed.

Lemma euttLF_eq_euttG_ r t1 t2:
  euttF RR (rfst r) (rsnd r) (observe t1) (observe t2) <-> euttG_ r (inr (t1,t2)).
Proof. reflexivity. Qed.

Global Arguments euttH h hg r rg t1%itree t2%itree.
Global Arguments euttL h hg r rg t1%itree t2%itree.

End EUTTG.

Hint Constructors euttHF.
Hint Unfold euttG_.
Hint Resolve monotone_euttG_ : paco.

Section EUTT_inftaus.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  
Inductive taus_one {R} (P: itree E R -> Prop) : itree' E R -> Prop :=
| to_step t (BASE: P t) : taus_one P (TauF t)
.
Hint Constructors taus_one.

Definition inftaus_ {R} P t := @taus_one R P (observe t).

Lemma mono_inftaus_ {R} : monotone1 (@inftaus_ R).
Proof.
  red; intros. red. destruct IN. eauto.
Qed.
Hint Resolve mono_inftaus_ : paco.

Definition inftaus {R} t := gcpn1 (@inftaus_ R) bot1 bot1 t.

(* TODO: think about avoiding classical axiom. *)
Lemma inftaus_or_fintaus {R} (t: itree E R) :
  inftaus t \/ exists t', unalltaus t t'.
Proof.
  destruct (classic (exists t', unalltaus t t')); eauto.
  left. revert t H. gcofix CIH.
  intros. gstep. red. destruct (observe t) eqn:EQ.
  - exfalso. apply H0. eexists. rewrite EQ. eauto.
  - econstructor; eauto. gbase. apply CIH.
    intros [t' [UNT NOT]]. apply H0.
    exists t'. eauto.
  - exfalso. apply H0. eexists. rewrite EQ. eauto.
Qed.

Lemma eutt_inf_not_fin t1 t2 t3
      (REL: @eutt E R1 R2 RR t1 t2)
      (INF: inftaus t1)
      (UNA: unalltaus t2 t3):
  False.
Proof.
  destruct UNA as [UNT NOT]. gunfold REL. red in REL.
  gunfold INF. red in INF.
  hinduction UNT before RR; intros.
  - hinduction REL before RR; intros; inv INF; eauto.
    eapply IHREL; eauto.
    gunfold BASE. eauto.
  - subst. eapply IHUNT; eauto.
    eapply gcpn2_unfold with (gf := eutt_ RR); eauto with paco.
    eapply eutt_elim_tauR.
    gstep. apply REL.
Qed.

End EUTT_inftaus.

Hint Constructors taus_one.
Hint Resolve mono_inftaus_ : paco.

Lemma eutt_coind {E R1 R2 RR} (P: _ -> _ -> Prop)
      (INF: forall ot1 ot2 (INF1: inftaus (go ot1)) (INF2: inftaus (go ot2)), P ot1 ot2)
      (RET: forall r1 r2
               (IN: RR r1 r2 : Prop),
          P (RetF r1) (RetF r2))
      (VIS: forall u e k1 k2
               (IN: forall x : u, eutt RR (k1 x) (k2 x)),
            P (VisF e k1) (VisF e k2))
      (TAUL: forall t1 ot2 (EQV: eutt RR t1 (go ot2)) (IN: P (observe t1) ot2),
             P (TauF t1) ot2)
      (TAUR: forall ot1 t2 (EQV: eutt RR (go ot1) t2) (IN: P ot1 (observe t2)),
             P ot1 (TauF t2))
  : forall t1 t2, @eutt E R1 R2 RR t1 t2 -> P (observe t1) (observe t2).
Proof.
  intros. subst.
  destruct (inftaus_or_fintaus t1) as [INF1 | FIN1], (inftaus_or_fintaus t2) as [INF2 | FIN2]; eauto.
  - eapply INF.
    + gstep. gunfold INF1. eauto.
    + gstep. gunfold INF2. eauto.
  - destruct FIN2. exfalso. eapply eutt_inf_not_fin; eauto.
  - destruct FIN1. exfalso.
    eapply Symmetric_eutt_hetero with (RR2 := flip RR) in H; eauto.
    eapply eutt_inf_not_fin; eauto.
  - destruct FIN1 as [t1' [UNT1 NOT1]], FIN2 as [t2' [UNT2 NOT2]].
    gunfold H. red in H. simpl in *.
    hinduction UNT1 before TAUR; intros.
    + hinduction UNT2 before TAUR; intros.
      * inv H; try contradiction; eauto.
        eapply VIS. intros. edestruct EUTTK; eauto. contradiction.
      * subst. inv H; try contradiction.
        eapply TAUR; eauto.
        gstep. eauto.
    + subst. eapply TAUL; eauto.
      * eapply eutt_elim_tauL. gstep. apply H.
      * eapply IHUNT1; eauto.
        eapply gcpn2_unfold with (gf:= eutt_ RR); eauto with paco.
        eapply eutt_elim_tauL. gstep. apply H.
Qed.

Section EUTTG_Lemmas.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).
  
Definition pswap {E R1 R2} (p: itree E R1 * itree E R2 + itree E R1 * itree E R2) :=
  match p with
  | inl (t1, t2) => inl (t2, t1)
  | inr (t1, t2) => inr (t2, t1)                      
  end.

Lemma euttG_sym p (REL: euttG RR bot1 bot1 p):
  @euttG E _ _ (flip RR) bot1 bot1 (pswap p).
Proof.
  revert p REL. gcofix CIH. intros.
  gstep. gunfold REL. destruct p, p; repeat red.
  - inv REL.
    econstructor; eauto. gbase. apply (CIH (inr (_,_))).
    eauto using rfst_mon, rsnd_mon, gcpn1_mon_bot with paco.
  - repeat red in REL.
    hinduction REL before CIH; eauto.
    + econstructor. gbase. apply (CIH (inr (_,_))).
      eauto using rfst_mon, rsnd_mon, gcpn1_mon_bot with paco.
    + econstructor; eauto. intros. destruct (EUTTK x).
      * left. gbase. apply (CIH (inl (_,_))).
        eauto using rfst_mon, rsnd_mon, gcpn1_mon_bot with paco.
      * right. gbase. apply (CIH (inr (_,_))).
        eauto using rfst_mon, rsnd_mon, gcpn1_mon_bot with paco.
Qed.  

Lemma euttL_bot t1 t2:
      @euttL E R1 R2 RR bot2 bot2 bot2 bot2 t1 t2 <->
      rsnd (euttG RR bot1 bot1) t1 t2.
Proof.
  split; intros.
  - eapply rsnd_mon; eauto; intros.
    eapply gcpn1_mon; eauto using rpair_bot with paco.
  - eapply gcpn1_mon; eauto with paco; contradiction.
Qed.

Lemma euttH_bot t1 t2:
      @euttH E R1 R2 RR bot2 bot2 bot2 bot2 t1 t2 <->
      euttG RR bot1 bot1 (inl (t1, t2)).
Proof.
  split; intros.
  - eapply rfst_mon; eauto; intros.
    eapply gcpn1_mon; eauto using rpair_bot with paco.
  - eapply gcpn1_mon; eauto with paco; contradiction.
Qed.

Lemma euttL_elim_tauL (t1: itree E R1) (t2: itree E R2)
    (REL : euttL RR bot2 bot2 bot2 bot2 (Tau t1) t2) :
  euttL RR bot2 bot2 bot2 bot2 t1 t2.
Proof.
  apply euttL_bot in REL.
  gunfold REL. gstep. red in REL. repeat red. simpl in *.
  remember (TauF t1) as ott1.
  hinduction REL before RR; intros; subst; try dependent destruction Heqott1; eauto.
  - econstructor. gunfold EQTAUS.
    eapply euttF_mon; eauto using rfst_mon, rsnd_mon, gcpn1_mon_bot with paco.
  - eapply euttF_mon; eauto using rfst_mon, rsnd_mon, gcpn1_mon_bot with paco.
Qed.

Lemma euttL_elim_tauR (t1: itree E R1) (t2: itree E R2)
    (REL : euttL RR bot2 bot2 bot2 bot2 t1 (Tau t2)) :
  euttL RR bot2 bot2 bot2 bot2 t1 t2.
Proof.
  apply euttL_bot in REL.
  gunfold REL. gstep. red in REL. repeat red. simpl in *.
  remember (TauF t2) as ott2.
  hinduction REL before RR; intros; subst; try dependent destruction Heqott2; eauto.
  - econstructor. gunfold EQTAUS.
    eapply euttF_mon; eauto using rfst_mon, rsnd_mon, gcpn1_mon_bot with paco.
  - eapply euttF_mon; eauto using rfst_mon, rsnd_mon, gcpn1_mon_bot with paco.
Qed.

Lemma euttL_unalltaus t1 t1' t2
      (NOT: unalltaus t1 t1')
      (EQ : @euttL E R1 R2 RR bot2 bot2 bot2 bot2 t1 t2):
  exists t2', unalltaus t2 t2'.
Proof.
  apply euttL_bot in EQ. gunfold EQ. repeat red in EQ. unfold unalltaus in *.
  destruct NOT as [UNT NOT].
  hinduction UNT before RR; intros.
  - hinduction EQ before RR; intros; subst; try inv NOT.
    + eexists (Ret r2). split; simpl; eauto.
    + eexists (Vis e k2). split; simpl; eauto.
    + edestruct IHEQ; eauto.
      exists x. split; eauto.
  - edestruct IHUNT; eauto. subst.
    eapply gcpn1_unfold with (gf := euttG_ RR) (x0 := inr (t', t2)); eauto with paco.
    apply euttL_bot. apply euttL_elim_tauL. apply euttL_bot. gstep. eauto.
Qed.

Lemma euttL_untaus t1 t2 t1'
      (EQ: @euttL E R1 R2 RR bot2 bot2 bot2 bot2 t1 t2)
      (UN: untaus t1 t1'):
  euttL RR bot2 bot2 bot2 bot2 t1' t2.
Proof.
  genobs t1 ot1. genobs t1' ot1'.
  hinduction UN before RR; intros.
  - (* TODO: [rewite (simpobs Heqot1) in EQ] takes a few seconds. *)
    apply euttL_bot in EQ. apply euttL_bot.
    gunfold EQ. gstep. repeat red in EQ |- *. simpobs.
    eauto.
  - subst. hexploit IHUN; cycle 1; eauto.
    apply euttL_elim_tauL.
    apply euttL_bot in EQ. apply euttL_bot.
    gunfold EQ. gstep. repeat red in EQ |- *. simpobs.
    eauto.
Qed.

Lemma euttHF_elim_tauL t1 ot2 clo r
      (IN: euttHF (rfst (rclo1 (euttG_ RR) clo r)) (rsnd (rclo1 (euttG_ RR) clo r)) (observe t1) ot2):
  @euttHF E R1 R2 (rfst (rclo1 (euttG_ RR) clo r)) (rsnd (rclo1 (euttG_ RR) clo r)) (TauF t1) ot2.
Proof.
  inv IN.
  econstructor; eauto.
  rewrite <-EQ1, <-itree_eta, tau_eutt. reflexivity.
Qed.

Lemma euttHF_elim_tauR t2 ot1 clo r
      (IN: euttHF (rfst (rclo1 (euttG_ RR) clo r)) (rsnd (rclo1 (euttG_ RR) clo r)) ot1 (observe t2)):
  @euttHF E R1 R2 (rfst (rclo1 (euttG_ RR) clo r)) (rsnd (rclo1 (euttG_ RR) clo r)) ot1 (TauF t2).
Proof.
  inv IN.
  econstructor; eauto.
  rewrite <-EQ2, <-itree_eta, tau_eutt. reflexivity.
Qed.

End EUTTG_Lemmas.

Section EUTTG_upto.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

(* Up to Transitivity.

   [euttG_clo_trans]

 *)

Inductive clo_euttG_trans (r: eutt_rel) : @eutt_rel E R1 R2 :=
| clo_euttG_trans_high t1 t2 t3 t4
      (EQVL: t1 ≈ t2)
      (EQVR: t4 ≈ t3)
      (REL: r (inl (t2, t3))) :
  clo_euttG_trans r (inl (t1,t4))
| clo_euttG_trans_low t1 t2 t3 t4
      (EQVL: t1 ≅ t2)
      (EQVR: t4 ≅ t3)
      (REL: r (inr (t2, t3))) :
  clo_euttG_trans r (inr (t1,t4))
.
Hint Constructors clo_euttG_trans.

Lemma euttG_clo_trans:
  clo_euttG_trans <2= cpn1 (euttG_ RR).
Proof.
  ucompat. constructor; [pmonauto|].
  intros. destruct PR.
  { inv REL.
    econstructor; cycle -1.
    + apply rclo1_base. apply RBASE.      
    + rewrite EQVL, EQ1. reflexivity.
    + rewrite EQVR, EQ2. reflexivity.
  }
  { gunfold EQVL. gunfold EQVR. red in EQVL, EQVR. repeat red. repeat red in REL.
    genobs_clear t1 ot1. genobs_clear t2 ot2. genobs_clear t3 ot3. genobs_clear t4 ot4.
    move REL before r. revert_until REL.
    induction REL; intros; subst.
    - dependent destruction EQVL. dependent destruction EQVR. simpobs.
      eauto.
    - dependent destruction EQVL. dependent destruction EQVR. simpobs.
      econstructor. apply rclo1_clo.
      econstructor; cycle -1.
      + apply rclo1_base. apply EQTAUS.
      + eauto.
      + eauto.
    - dependent destruction EQVL. dependent destruction EQVR. simpobs.
      econstructor. intros.
      edestruct EUTTK.
      + left. apply rclo1_clo. econstructor; cycle -1.
        * apply rclo1_base. apply H.
        * rewrite (REL x). reflexivity.
        * rewrite (REL0 x). reflexivity.
      + right. apply rclo1_clo. econstructor; cycle -1.
        * apply rclo1_base. apply H.
        * eauto.
        * eauto.
    - dependent destruction EQVL.
      econstructor. eapply IHREL; eauto.
      gunfold REL0. eauto.
    - dependent destruction EQVR.
      econstructor. eapply IHREL; eauto.
      gunfold REL0. eauto.
  }
Qed.

(* Up to Bind

   [euttG_clo_bind]
 *)

Inductive clo_euttG_bind (r: eutt_rel) : @eutt_rel E R1 R2 :=
| clo_euttG_bind_high U1 U2 RU t1 t2 k1 k2
      (EQV: @eutt E U1 U2 RU t1 t2)
      (REL: forall v1 v2 (RELv: RU v1 v2), r (inl (k1 v1, k2 v2)))
  : clo_euttG_bind r (inl (ITree.bind t1 k1, ITree.bind t2 k2))
| clo_euttG_bind_low U1 U2 RU t1 t2 k1 k2
      (EQV: @eutt E U1 U2 RU t1 t2)
      (REL: forall v1 v2 (RELv: RU v1 v2), r (inr (k1 v1, k2 v2)))
  : clo_euttG_bind r (inr (ITree.bind t1 k1, ITree.bind t2 k2))
.
Hint Constructors clo_euttG_bind.

Lemma euttG_clo_bind:
  clo_euttG_bind <2= cpn1 (euttG_ RR).
Proof.
  ucompat. constructor; [pmonauto|]. 
  intros. destruct PR.
  (* 
     euttH 
   *)
  { repeat red.
    rewrite !unfold_bind, (itree_eta' (observe t1)), (itree_eta' (observe t2)), <- !unfold_bind.
    pattern (observe t1), (observe t2).
    revert t1 t2 EQV.
    eapply eutt_coind; intros.
    (* INF *)
    { econstructor; try (rewrite <-itree_eta; reflexivity).
      red. apply rclo1_cpn.
      remember (go ot1) as t1. remember (go ot2) as t2. clear ot1 Heqt1 ot2 Heqt2.
      revert t1 t2 INF1 INF2.
      ucofix CIH. intros.
      gunfold INF1. inv INF1. gunfold INF2. inv INF2.
      repeat red. cbn in *.
      rewrite !unfold_bind; simpobs. cbn.
      econstructor. ubase. eapply CIH; eauto.
    }
    (* RET *)
    { specialize (REL _ _ IN). inv REL.
      econstructor; cycle -1.
      * eauto with rclo paco.
      * rewrite <-EQ1, <-!itree_eta, bind_ret. reflexivity.
      * rewrite <-EQ2, <-!itree_eta, bind_ret. reflexivity.
    }
    (* VIS *)
    { econstructor.
      - rewrite <-itree_eta, bind_vis. reflexivity.
      - rewrite <-itree_eta, bind_vis. reflexivity.
      - eapply rclo1_step. econstructor.
        left. eapply rclo1_clo. econstructor; eauto.
        intros. eapply rclo1_step.
        eapply monotone_euttG_; eauto with rclo.
    }
    (* TAUL *)
    { cbn in *. apply euttHF_elim_tauL. eauto.
    }
    (* TAUR *)
    { cbn in *. apply euttHF_elim_tauR. eauto.
    }
  }
  
  (* 
     euttL 
   *)
  { gunfold EQV. red in EQV. repeat red.
    rewrite !unfold_bind, <-(unfold_bind (go (observe t1))), <-(unfold_bind (go (observe t2))).
    genobs_clear t1 ot1. genobs_clear t2 ot2. revert k1 k2 REL.
    induction EQV; simpl; intros.
    - rewrite !bind_ret. eapply euttF_mon; eauto with rclo paco. 
    - rewrite !bind_tau. econstructor.
      apply rclo1_clo. econstructor; eauto.
      intros. specialize (REL _ _ RELv).
      eapply rclo1_step.
      eapply euttF_mon; eauto.
      + intros. apply rclo1_base, PR.
      + intros. apply rclo1_base, PR.
    - rewrite !bind_vis. econstructor. intros. specialize (EUTTK x).
      destruct EUTTK; try contradiction.
      right. apply rclo1_clo. econstructor; eauto.
      intros. specialize (REL _ _ RELv).
      apply rclo1_step. eapply euttF_mon; eauto.
      + intros. apply rclo1_base, PR.
      + intros. apply rclo1_base, PR.
    - rewrite !bind_tau. econstructor.
      specialize (IHEQV _ _ REL).
      eapply euttF_mon; eauto.
    - rewrite !bind_tau. econstructor.
      specialize (IHEQV _ _ REL).
      eapply euttF_mon; eauto.
  }
Qed.

(* Up to Taus: a collorary of [euttG_clo_trans] and [euttG_clo_bind]

   [euttG_clo_tausL]
   [euttG_clo_tausR]

 *)

Inductive clo_euttG_tausL (r: eutt_rel) : @eutt_rel E R1 R2 :=
| clo_euttG_taus_left_high t1 t1' t2
      (UNT: untaus t1 t1')
      (REL: r (inl (t1', t2))) :
    clo_euttG_tausL r (inl (t1, t2))
| clo_euttG_taus_left_low t1 t1' t2
      (UNT: untaus t1 t1')
      (REL: r (inr (t1', t2))) :
    clo_euttG_tausL r (inr (t1, t2))
.
Hint Constructors clo_euttG_tausL.

Inductive clo_euttG_tausR (r: eutt_rel) : @eutt_rel E R1 R2 :=
| clo_euttG_taus_right_high t1 t2 t2' 
      (UNT: untaus t2 t2')
      (REL: r (inl (t1, t2'))) :
    clo_euttG_tausR r (inl (t1, t2))
| clo_euttG_taus_right_low t1 t2 t2'
      (UNT: untaus t2 t2')
      (REL: r (inr (t1, t2'))) :
    clo_euttG_tausR r (inr (t1, t2))
.
Hint Constructors clo_euttG_tausR.

Lemma euttG_clo_tausL:
  clo_euttG_tausL <2= cpn1 (euttG_ RR).
Proof.
  intros. destruct PR.
  - uclo euttG_clo_trans. econstructor; cycle -1; eauto with paco.
    + eapply untaus_eutt. eauto.
    + reflexivity.
  - genobs t1 ot1. genobs t1' ot1'.
    hinduction UNT before RR; intros.
    + uclo euttG_clo_trans. econstructor; cycle -1; eauto with paco.
      * rewrite (simpobs Heqot1), (simpobs Heqot1'). reflexivity.
      * reflexivity.
    + subst. uclo euttG_clo_trans. econstructor.
      * instantiate (1:= Tau (Ret ()) ;; t').
        rewrite (simpobs Heqot1), bind_tau, bind_ret_. reflexivity.
      * instantiate (1:= Ret () ;; t2).
        rewrite bind_ret. reflexivity.
      * uclo euttG_clo_bind. econstructor; eauto.
        rewrite tau_eutt. reflexivity.
Qed.

Lemma euttG_clo_tausR:
  clo_euttG_tausR <2= cpn1 (euttG_ RR).
Proof.
  intros. destruct PR.
  - uclo euttG_clo_trans. econstructor; cycle -1; eauto with paco.
    + reflexivity.    
    + eapply untaus_eutt. eauto.
  - genobs t2 ot2. genobs t2' ot2'.
    hinduction UNT before RR; intros.
    + uclo euttG_clo_trans. econstructor; cycle -1; eauto with paco.
      * reflexivity.      
      * rewrite (simpobs Heqot2), (simpobs Heqot2'). reflexivity.
    + subst. uclo euttG_clo_trans. econstructor.
      * instantiate (1:= Ret () ;; t1).
        rewrite bind_ret. reflexivity.
      * instantiate (1:= Tau (Ret ()) ;; t').
        rewrite (simpobs Heqot2), bind_tau, bind_ret_. reflexivity.
      * uclo euttG_clo_bind. econstructor; eauto.
        rewrite tau_eutt. reflexivity.
Qed.

Global Instance eutt_cong_euttL h hg r rg:
  Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
         (@euttL E _ _ RR h hg r rg).
Proof.
  repeat intro.
  gclo euttG_clo_trans. econstructor; eauto.
Qed.

Global Instance eutt_cong_euttH h hg r rg:
  Proper (eutt eq ==> eutt eq ==> flip impl)
         (@euttH E _ _ RR h hg r rg).
Proof.
  repeat intro.
  gclo euttG_clo_trans. econstructor; eauto.
Qed.

End EUTTG_upto.

Arguments euttG_clo_trans : clear implicits.
Arguments euttG_clo_bind : clear implicits.
Arguments euttG_clo_tausL : clear implicits.
Arguments euttG_clo_tausR : clear implicits.

Section EUTTG_correct.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

Lemma euttLH_impl_eutt t1 t2 t1' t2'
      (EQ1: t1 ≈ t1')
      (EQ2: t2 ≈ t2')
      (IN: euttH RR bot2 bot2 bot2 bot2 t1 t2 \/
           euttL RR bot2 bot2 bot2 bot2 t1 t2):
  @eutt E _ _ RR t1' t2'.
Proof.
  revert_until RR. gcofix CIH.

  (*
    euttL
   *)
  assert (EUTTL: forall t1 t2 t1' t2'
                   (EQ1 : t1 ≈ t1') (EQ2 : t2 ≈ t2')
                   (IN : euttL RR bot2 bot2 bot2 bot2 t1 t2),
             gcpn2 (eutt_ RR) bot2 r t1' t2').
  { intros. apply euttL_bot in IN. gunfold IN. repeat red in IN.
    genobs t1 ot1. genobs t2 ot2.
    hinduction IN before CIH; intros.
    { hexploit @eutt_unalltaus_ret; try apply EQ1; try red; simpobs; simpl; eauto.
      intros [UNT'1 NOT'1]. rewrite (itree_eta' (RetF _)) in UNT'1.
      hexploit @eutt_unalltaus_ret; try apply EQ2; try red; simpobs; simpl; eauto.
      intros [UNT'2 NOT'2]. rewrite (itree_eta' (RetF _)) in UNT'2.
      gclo eutt_clo_tausL. econstructor; [apply UNT'1|].
      gclo eutt_clo_tausR. econstructor; [apply UNT'2|].
      gstep. econstructor. eauto.
    }
    { apply euttL_bot in EQTAUS.
      assert (EUTT1: t1 ≈ t1').
      { rewrite <-EQ1, (simpobs Heqot1), tau_eutt. reflexivity. }
      assert (EUTT2: t2 ≈ t2').
      { rewrite <-EQ2, (simpobs Heqot2), tau_eutt. reflexivity. }
      assert (DEC: (~ notauF (observe t1')) /\ ~ (notauF (observe t2')) \/
                   (finite_taus t1 /\ finite_taus t2 /\ finite_taus t1' /\ finite_taus t2')).
      { destruct (notau_dec (observe t1')).
        - destruct (notau_dec (observe t2')); eauto.
          right. symmetry in EUTT2.
          hexploit @eutt_unalltaus; try apply EUTT2; eauto. intros [tx2 [UNT2 NOT2]].
          apply euttL_bot, euttG_sym, euttL_bot in EQTAUS.
          hexploit @euttL_unalltaus; try apply EQTAUS; eauto. intros [tx1 [UNT1 NOT1]].
          hexploit @eutt_unalltaus; try apply EUTT1; eauto. intros [tx1' [UNT1' NOT1']].
          repeat split; eauto.
        - right. symmetry in EUTT1.
          hexploit @eutt_unalltaus; try apply EUTT1; eauto. intros [tx1 [UNT1 NOT1]].
          hexploit @euttL_unalltaus; try apply EQTAUS; eauto. intros [tx2 [UNT2 NOT2]].
          hexploit @eutt_unalltaus; try apply EUTT2; eauto. intros [tx2' [UNT2' NOT2']].
          repeat split; eauto.
      }
      destruct DEC.
      { gstep. red. genobs t1' ot1'; genobs t2' ot2'.
        destruct ot1', ot2'; simpl in *; inv H; try contradiction.
        econstructor. gbase. eapply CIH; cycle -1.
        - right. apply EQTAUS.
        - rewrite <-(tau_eutt t1), <-(tau_eutt t).
          rewrite <-(simpobs Heqot1), <-(simpobs Heqot1'). eauto.
        - rewrite <-(tau_eutt t2), <-(tau_eutt t4).
          rewrite <-(simpobs Heqot2), <-(simpobs Heqot2'). eauto.
      }
      { destruct H as [[otx1 [UNT1 NOT1]] [[otx2 [UNT2 NOT2]]
                      [[otx1' [UNT1' NOT1']] [otx2' [UNT2' NOT2']]]]].
        gclo eutt_clo_tausL. econstructor; [instantiate (1:= go _); eauto|].
        gclo eutt_clo_tausR. econstructor; [instantiate (1:= go _); eauto|].
        eapply euttL_untaus in EQTAUS; [|instantiate (1:= go _); eauto].
        eapply euttL_bot, euttG_sym, euttL_bot in EQTAUS.        
        eapply euttL_untaus in EQTAUS; [|instantiate (1:= go _); eauto].
        eapply euttL_bot, euttG_sym, euttL_bot in EQTAUS.
        rewrite itree_eta' in UNT1. rewrite itree_eta' in UNT2.
        rewrite itree_eta' in UNT1'. rewrite itree_eta' in UNT2'.
        assert (EQx1: (go otx1) ≈ (go otx1')).
        { rewrite <-(untaus_eutt UNT1), EUTT1, (untaus_eutt UNT1'). reflexivity. }
        assert (EQx2: (go otx2) ≈ (go otx2')).
        { rewrite <-(untaus_eutt UNT2), EUTT2, (untaus_eutt UNT2'). reflexivity. }
        gstep. red. simpl in *. apply euttL_bot in EQTAUS.
        gunfold EQTAUS. gunfold EQx1. gunfold EQx2. red in EQx1, EQx2.
        inv EQTAUS; simpl in *; subst; try contradiction.
        - inv EQx1; simpobs; try contradiction.
          inv EQx2; simpobs; try contradiction.
          eauto.
        - dependent destruction EQx1; simpobs; try contradiction.
          dependent destruction EQx2; simpobs; try contradiction.
          econstructor. right. gbase. eapply CIH; cycle -1.
          + edestruct EUTTK1.
            * left. apply euttH_bot. eauto.
            * right. apply euttL_bot. eauto.
          + edestruct EUTTK; eauto; try contradiction.
          + edestruct EUTTK0; eauto; try contradiction.
      }
    }
    { hexploit @eutt_unalltaus_vis; try apply EQ1; try red; simpobs; simpl; eauto.
      intros [k'1 [UNT'1 EQ'1]]. rewrite (itree_eta' (VisF _ _)) in UNT'1.
      hexploit @eutt_unalltaus_vis; try apply EQ2; try red; simpobs; simpl; eauto.
      intros [k'2 [UNT'2 EQ'2]]. rewrite (itree_eta' (VisF _ _)) in UNT'2.
      gclo eutt_clo_tausL. econstructor; [apply UNT'1|].
      gclo eutt_clo_tausR. econstructor; [apply UNT'2|].
      gstep. econstructor. intros. right.
      gbase. eapply CIH; eauto.
      destruct (EUTTK x).
      - left. apply euttH_bot. eauto.
      - right. apply euttL_bot. eauto.
    }
    { eapply IHIN; cycle -2; eauto.
      rewrite <-EQ1, (simpobs Heqot1), tau_eutt. reflexivity.
    }
    { eapply IHIN; cycle -2; eauto.
      rewrite <-EQ2, (simpobs Heqot2), tau_eutt. reflexivity.
    }
  }

  intros. destruct IN as [IN | IN]; [|eapply EUTTL; eauto].
  
  (*
    euttH
   *)
  eapply gcpn1_mon in IN; try apply rpair_bot; eauto with paco.
  gunfold IN. inv IN.
  apply euttL_bot in RBASE.
  eapply EUTTL, RBASE.
  - rewrite <-EQ0, <-itree_eta. eauto.
  - rewrite <-EQ3, <-itree_eta. eauto.
Qed.

Lemma eutt_impl_euttL t1 t2
      (EQ: @eutt E _ _ RR t1 t2):
  euttL RR bot2 bot2 bot2 bot2 t1 t2.
Proof.
  revert_until RR. gcofix CIH. intros.
  gunfold EQ. gstep. red in EQ. repeat red.
  induction EQ; eauto.
  - econstructor. gbase. eauto.
  - econstructor. intros. destruct (EUTTK x); try contradiction.
    right. gbase. eauto.
Qed.

Lemma euttL_impl_euttH t1 t2
      (EQ: @euttL E _ _ RR bot2 bot2 bot2 bot2 t1 t2):
  euttH RR bot2 bot2 bot2 bot2 t1 t2.
Proof.
  gstep. econstructor; eauto; rewrite <-itree_eta; reflexivity.
Qed.

Lemma euttH_impl_eutt t1 t2
      (IN: euttH RR bot2 bot2 bot2 bot2 t1 t2):
  @eutt E _ _ RR t1 t2.
Proof.
  eapply euttLH_impl_eutt; eauto; reflexivity.
Qed.




(* Test *)


(* Lemma euttL_fix h hg r rg x *)
(*       (LEh: h <2= hg) (LEr: r <2= rg) *)
(*       (EQ: x <2= euttL RR h (x \2/ hg) r (x \2/ rg)): *)
(*   x <2= @euttL E R1 R2 RR h hg r rg. *)
(* Proof. *)
(*   cut (rpair x x <1= euttG RR (rpair h r) (rpair hg rg)). *)
(*   { intros. apply H. eauto. } *)

(*   gcofix CIH. *)
(*   intros. destruct x1, p. *)
(*   - gstep. econstructor; try (rewrite <-itree_eta; reflexivity). *)
(*     eapply gcpn1_mon; try apply EQ; eauto with paco. *)
(*     intros. destruct x0, p; simpl in *; destruct PR0; eauto. *)
(*   - eapply gcpn1_mon; try apply EQ; eauto with paco. *)
(*     intros. destruct x0, p; simpl in *; destruct PR0; eauto. *)
(* Qed. *)

(* Lemma euttH_fix h hg r rg x *)
(*       (LEh: h <2= hg) (LEr: r <2= rg) *)
(*       (EQ: x <2= euttH RR h (x \2/ hg) (h \2/ r) rg): *)
(*   x <2= @euttH E R1 R2 RR h hg r rg. *)
(* Proof. *)
(*   cut (rpair x x <1= euttG RR (rpair h r) (rpair hg rg)). *)
(*   { intros. apply H. eauto. } *)

(*   gcofix CIH; eauto using rpair_mon. *)
(*   intros. destruct x1, p. *)
(*   - gstep. econstructor; try (rewrite <-itree_eta; reflexivity). *)
(*     eapply gcpn1_mon; try apply EQ; eauto using rpair_mon with paco. *)
(*     intros. destruct x0, p; simpl in *; destruct PR0; eauto. *)
(*   - eapply gcpn1_mon; try apply EQ; eauto with paco. *)
(*     intros. destruct x0, p; simpl in *; destruct PR0; eauto. *)
(* Qed. *)

(* Lemma foo r r' *)
(*       (LE: rsnd r <2= rfst r'): *)
(*   rsnd (cpn1 (euttG_ RR) r) <2= rfst (cpn1 (@euttG_ E R1 R2 RR) r'). *)
(* Proof. *)
(*   intros. repeat red  *)
  
(*   ucofix CIH. *)
(*   intros. *)
(*   econstructor; cycle -1. *)
(*   - repeat red. repeat red in PR. *)


    
(*   - rewrite <-itree_eta. reflexivity. *)
(*   - rewrite <-itree
_eta. reflexivity. *)
(* Qed. *)

(* Inductive clo_euttG_euttL (r: eutt_rel) : @eutt_rel E R1 R2 := *)
(* | clo_euttL_intro t1 t2  *)
(*       (REL: euttL RR (rfst r) (rfst r) (rfst r) (rfst r) t1 t2) : *)
(*   clo_euttG_euttL r (inl(t1,t2)) *)
(* . *)
(* Hint Constructors clo_euttG_euttL. *)

(* Lemma euttG_clo_euttL: clo_euttG_euttL <2= cpn1 (euttG_ RR). *)
(* Proof. *)
(*   ucompat. econstructor. admit. *)
(*   intros. destruct PR. *)
(*   repeat red. repeat red in REL. *)
  
  

(*   econstructor; try (rewrite <-itree_eta; reflexivity). *)
(*   repeat red. *)
(*   apply rclo1_clo.  *)
  
(*   apply rclo1_step. *)
(*   repeat red. repeat red in REL. *)

  
  
  
  
(*   ucpn. *)
(*   ustep.  *)
(*   eapply cpn1_mon; eauto. *)
(*   intros. *)
(*   destruct PR. *)
(*   - destruct x1, p; simpl in *. *)
(*     + ubase. eauto. *)
(*     +  *)
  
  
(* Qed. *)

(* Lemma euttH_lower r: *)
(*   euttL RR r r r r <2= @euttH E _ _ RR r r bot2 bot2. *)
(* Proof. *)
(*   gcofix CIH. *)
(*   intros. *)

(*   repeat red in PR. *)
(*   repeat red. *)
(*   destruct PR. *)
(*   econstructor. *)
  
(* Qed.   *)

Inductive clo_trans (h: itree E R1 -> itree E R2 -> Prop) t1 t2 : Prop :=
| clo_trans_ t1' t2'  
             (EQ1: t1 ≈ t1')
             (EQ2: t2 ≈ t2')
             (REL: h t1' t2')
.
Hint Constructors clo_trans.

Axiom foo: forall r,
    cpn1 (euttG_ RR) r <1=
    (rpair (clo_trans (rfst r)) (clo_trans (rsnd r)) \1/ fcpn1 (euttG_ RR) r).

Lemma euttH_lower h:
  euttL RR h h h h <2= @euttH E _ _ RR h h bot2 bot2.
Proof.
  (* gcofix CIH.   *)
  intros.
  destruct PR.
  econstructor.
  ustep.
  
  
  eapply foo in IN.
  destruct IN; simpl in *.
  - destruct H.
    gclo euttG_clo_trans. econstructor; eauto.
    destruct REL.
    + destruct H.
      * gstep. econstructor; try (rewrite <-itree_eta; reflexivity).
        eauto with paco.
      * eauto with paco.
    + repeat red in H.
      gstep. repeat red.
      inv H.
      * econstructor; try reflexivity.
        gstep. econstructor. eauto.
      * econstructor; try reflexivity.
        red in EQTAUS.
        red.
        admit.
      * admit.
      * admit.
      * admit.
  - admit.

  EQ1 : x1 ≈ t1'
  EQ2 : x2 ≈ t2'
  H : euttF RR
      (rfst (cpn1 (euttG_ RR) (rpair h (r \2/ h))))
      (rsnd (cpn1 (euttG_ RR) (rpair h (r \2/ h))))
      (observe t1') 
      (observe t2')
  ============================
  gcpn1 (euttG_ RR) (rpair h r) r0 (inl (t1', t2'))

  H : euttF RR
      (rfst (cpn1 (euttG_ RR) (rpair h (r \2/ h))))
      (rsnd (cpn1 (euttG_ RR) (rpair h (r \2/ h))))
      (observe t1) (observe t2)
  ============================
  gcpn1 (euttG_ RR) (rpair h r) r0 (inl (t1, t2))
    
    
  intros.

  repeat red in PR.
  repeat red.
  destruct PR.
  econstructor.


  
  
  
  repeat red.
  destruct PR.






  
  gclo euttG_clo_euttL. econstructor.
  eapply gcpn1_mon; eauto with paco; intros.
  - destruct x2, p; simpl in *.
    + red. gbase. simpl.
      
  
  

  x <2= euttL h h h h
  x <2= euttH h h bot bot


  euttL r r r r               
  
  euttL (h \/ rg) <= euttL h 

        
  x <= euttH h hg r rg




  cut ((clo_trans h \2/ x) <2= euttL RR hg hg rg rg).
  { intros. gstep. econstructor; try (rewrite <-itree_eta; reflexivity).
    eapply H. eauto.
  }

  gcofix CIH.
  intros. destruct PR; cycle 1.
  - eapply IN in H.
    eapply gcpn1_mon; eauto with paco.
    intros. destruct x0, p.
    




    
  intros. gstep. econstructor.
  

  
  
  euttL (ret 1,ret 2) (ret1, ret 2) bot2 bot  
  
  euttH (ret 1,ret 2) (ret 1, ret 2) bot bot   (ret 1, ret 2)
  
  x\/clo(h) <= euttL hg hg rg (x\/clo(h) \/ rg)
  x\/clo(h) <= euttL hg hg rg rg
  x\/h <= euttH h hg r rg
  x   <= euttH h hg r rg                            




  

  
  intros. gstep. econstructor; try (rewrite <-itree_eta; reflexivity).
  revert x0 x1 PR.
  gcofix CIH. intros.
  eapply gcpn1_mon. eauto with paco. eapply IN.
    
  
  
  (* intros. repeat red. repeat red in PR. *)
  (* destruct PR. *)
  (* constructor. *)
  (* cut1 (cpn1 (euttG_ RR) (rpair h (h \2/ r) \1/ fcpn1 (euttG_ RR) (rpair hg rg)) (inl (x0,x1))  (inl (x0,x1))  *)

  (* intros. destruct H. econstructor. *)

  
  
  revert t1 t2.
  gcofix CIH. intros. destruct H0.
  gcpn. eapply cpn1_mon; eauto.
  intros.
  destruct PR; eauto with paco.
  econstructor.
  ubase. right.
  eapply fcpn1_mon; eauto with paco.
  intros.
  destruct x1, p; simpl in *; eauto.
  destruct PR; eauto.
  eapply CIH.
  
  

  
  gcofix CIH. intros.
  destruct PR. gcpn. eapply cpn1_mon; eauto.

  intros. destruct x0, p.
  - destruct PR; simpl in *; eauto with paco.
    
    
    repeat red in H.
    gstep. repeat red.
    eapply euttHF_mon; eauto; intros.
    + eapply rfst_mon; eauto. intros.
      gcpn. eapply cpn1_mon; eauto with paco.
    + eapply rsnd_mon; eauto. intros.
      gcpn. eapply cpn1_mon; eauto with paco.
  - destruct PR; simpl in *.
    + destruct H; eauto with paco.
      
      


  repeat red.
  repeat red in EQ.
  specialize (EQ _ _ PR).
  destruct EQ.
  econstructor.
  
euttL (h \2/ r)                       hg r rg
  
euttH (h \2/ euttL h hg r rg) hg r rg  


  eapply cpn1_mon; eauto. intros.
  destruct PR.
  - destruct x0, p; simpl in *.
    + ubase. left. simpl. eauto.
    + destruct H.
      * 

  
  destruct EQ. econstructor.
  
  
  
  eapply cpn1_mon; cycle 1.
  { intros. gstep. 
    econstructor.


    try rewrite <-itree_eta; try reflexivity.
  repeat red in EQ. repeat red.
  
  
Qed.



  
End EUTTG_correct.























(** ** Tactics *)

(** Remove all taus from the left hand side of the goal
    (assumed to be of the form [lhs ≈ rhs]). *)
Ltac tau_steps :=
  repeat (
      (* Only rewrite the LHS, even if it also occurs in the RHS *)
      rewrite itree_eta at 1;
      cbn;
      match goal with
      | [ |- go (observe _) ≈ _ ] =>
        (* Cancel [itree_eta] if no progress was made. *)
        fail 1
      | _ => try rewrite tau_eutt
      end).


Global Instance eutt_cong_gcpn_ (r rg: itree E R1 -> itree E R2 -> Prop) :
  Proper (eutt eq ==> eutt eq ==> impl)
         (gcpn2 (@eutt0 E R1 R2 RR) r rg).
Proof.
  repeat intro.
  gclo eutt_clo_trans_left. econstructor. symmetry. eauto.
  gclo eutt_clo_trans_right. econstructor. symmetry. eauto.
  eauto.
Qed.

Global Instance eutt_cong_gcpn (r rg: itree E R1 -> itree E R2 -> Prop) :
  Proper (eutt eq ==> eutt eq ==> iff)
         (gcpn2 (@eutt0 E R1 R2 RR) r rg).
Proof.
  split; apply eutt_cong_gcpn_; auto using symmetry.
Qed.

Definition eutt_eq_under_rr_impl_ :
  Proper (@eutt E _ _ eq ==> @eutt _ _ _ eq ==> flip impl) (eutt RR).
Proof.
  repeat intro. red. rewrite H, H0. eauto with paco.
Qed.

Global Instance eutt_eq_under_rr_impl :
  Proper (@eutt E _ _ eq ==> @eutt _ _ _ eq ==> iff) (eutt RR).
Proof.
  split; apply eutt_eq_under_rr_impl_; auto using symmetry.
Qed.

Global Instance eutt_bind {E U R} :
  Proper (pointwise_relation _ (eutt eq) ==>
          eutt eq ==>
          eutt eq) (@ITree.bind' E U R).
Proof.
  gclo eutt_clo_bind. econstructor; eauto.
  intros. subst. eauto with paco.
Qed.

Global Instance eq_cong_eutt0 r rg r0 rg0:
  Proper (eq_itree eq ==> eq_itree eq ==> iff)
         (gcpn2 (@eutt0_ E R1 R2 RR (gcpn2 (eutt0 RR) r rg)) r0 rg0).
Proof.
  split; apply eq_cong_eutt0_; auto; symmetry; auto.
Qed.

Section EUTT_eq2.

Context {E : Type -> Type} {R : Type}.

Local Notation eutt := (@eutt E R R eq).

Global Instance Transitive_eutt : Transitive eutt.
Proof.
  repeat intro. rewrite H, H0. reflexivity.
Qed.

(* We can now rewrite with [eutt] equalities. *)
Global Instance Equivalence_eutt : @Equivalence (itree E R) eutt.
Proof. constructor; typeclasses eauto. Qed.

End EUTT_eq2.

Global Instance eutt_map {E R S} :
  Proper (pointwise_relation _ eq ==> eutt eq ==> eutt eq) (@ITree.map E R S).
Proof.
  unfold ITree.map. do 3 red. intros.
  rewrite H0. setoid_rewrite H. reflexivity.
Qed.

Global Instance eutt_forever {E R S} :
  Proper (eutt eq ==> eutt eq) (@ITree.forever E R S).
Proof.
  gstep. gcofix CIH'. intros.
  rewrite (unfold_forever x), (unfold_forever y).
  gclo eutt0_clo_bind. econstructor; eauto.
  intros. subst. gstep. econstructor. eauto with paco.
Qed.

(** Generalized heterogeneous version of [eutt_bind] *)
Lemma eutt_bind_gen {E R1 R2 S1 S2} {RR: R1 -> R2 -> Prop} {SS: S1 -> S2 -> Prop}:
  forall t1 t2,
    eutt RR t1 t2 ->
    forall s1 s2, (forall r1 r2, RR r1 r2 -> eutt SS (s1 r1) (s2 r2)) ->
                  @eutt E _ _ SS (ITree.bind t1 s1) (ITree.bind t2 s2).
Proof.
  gclo eutt_clo_bind. eauto 7 with paco.
Qed.

Lemma unfold_aloop {E A B} (f : A -> itree E A + B) (x : A) :
    ITree.aloop f x
  ≈ ITree._aloop id (ITree.aloop f) (f x).
Proof.
  rewrite unfold_aloop'; unfold ITree._aloop.
  destruct f.
  - rewrite tau_eutt; reflexivity.
  - reflexivity.
Qed.

Lemma bind_aloop {E A B C} (f : A -> itree E A + B) (g : B -> itree E B + C): forall x,
    (ITree.aloop f x >>= ITree.aloop g)
  ≈ ITree.aloop (fun ab =>
       match ab with
       | inl a => inl (ITree._aloop id (fun a => Ret (inl a))
                                    (bimap (id_ _) inr (f a)))
       | inr b => bimap (ITree.map inr) (id_ _) (g b)
       end) (inl x).
Proof.
  gstep. gcofix CIH. intros.
  rewrite !unfold_aloop'. unfold ITree._aloop.
  destruct (f x) as [t | b]; cbn.
  - unfold id. rewrite bind_tau. gstep. constructor.
    rewrite !bind_bind.
    gclo eutt0_clo_bind. econstructor.
    { reflexivity. }
    intros ? _ [].
    rewrite bind_ret.
    eauto with paco.
  - rewrite bind_ret_. apply eutt0_tau_right.
    rewrite bind_ret_.
    revert b. gcofix CIH'. intros.
    rewrite !unfold_aloop'. unfold ITree._aloop.
    destruct (g b) as [t' | c]; cbn.
    + rewrite map_bind. gstep. constructor.
      gclo eutt0_clo_bind. econstructor; [reflexivity|].
      intros. subst. eauto with paco.
    + gstep. econstructor. reflexivity.
Qed.
