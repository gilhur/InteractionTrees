(** * Shallow equivalence *)

(** Equality under [observe]:

[[
  observing eq t1 t2 <-> t1.(observe) = t2.(observe)
]]

  We actually define a more general relation transformer
  [observing] to lift arbitrary relations through [observe]. *)

From ITree Require Import Core.ITreeDefinition.

From Coq Require Import
     Classes.RelationClasses
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations
     ProofIrrelevance.


(** ** Misc *)

(** Rewrite all heterogeneous equalities with the axiom
    [inj_pair2 : existT _ T a = existT _ T b -> a = b]. *)
Ltac auto_inj_pair2 :=
  repeat (match goal with
          | [ H : _ |- _ ] => apply inj_pair2 in H
          end).

Lemma pointwise_relation_fold {A B} {r: relation B} f g :
  (forall v:A, r (f v) (g v)) -> pointwise_relation _ r f g.
Proof. red. eauto. Qed.

(**)

(** ** [observing]: Lift relations through [observe]. *)
Inductive observing {E R1 R2}
           (eq_ : itree' E R1 -> itree' E R2 -> Prop)
           (t1 : itree E R1) (t2 : itree E R2) : Prop :=
| observing_intros :
    eq_ t1.(observe) t2.(observe) -> observing eq_ t1 t2.
Hint Constructors observing.

Section observing_relations.

Context {E : Type -> Type} {R : Type}.
Variable (eq_ : itree' E R -> itree' E R -> Prop).

Global Instance observing_observe :
  Proper (observing eq_ ==> eq_) (@observe E R).
Proof. intros ? ? []; cbv; auto. Qed.

Global Instance observing_go : Proper (eq_ ==> observing eq_) (@go E R).
Proof. cbv; auto. Qed.

Global Instance monotonic_observing eq_' :
  subrelation eq_ eq_' ->
  subrelation (observing eq_) (observing eq_').
Proof. intros ? ? ? []; cbv; eauto. Qed.

Global Instance Equivalence_observing :
  Equivalence eq_ -> Equivalence (observing eq_).
Proof.
  intros []; split; cbv; auto.
  - intros ? ? []; auto.
  - intros ? ? ? [] []; eauto.
Qed.

End observing_relations.

Lemma unfold_bind {E R S}
      (t : itree E R) (k : R -> itree E S) :
  observing eq
    (ITree.bind t k)
    (ITree._bind k (fun t => ITree.bind t k) (observe t)).
Proof. eauto. Qed.

Global Instance observing_bind {E R S} :
  Proper (eq ==> observing eq ==> observing eq) (@ITree.bind' E R S).
Proof.
  repeat intro; subst.
  do 2 rewrite unfold_bind; rewrite H0.
  reflexivity.
Qed.

Lemma bind_ret {E R S} (r : R) (k : R -> itree E S) :
  observing eq (ITree.bind (Ret r) k) (k r).
Proof. apply unfold_bind. Qed.

Lemma bind_tau {E R} U t (k: U -> itree E R) :
  observing eq (ITree.bind (Tau t) k) (Tau (ITree.bind t k)).
Proof. apply @unfold_bind. Qed.

Lemma bind_vis {E R U V} (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  observing eq
    (ITree.bind (Vis e ek) k)
    (Vis e (fun x => ITree.bind (ek x) k)).
Proof. apply @unfold_bind. Qed.

Lemma unfold_aloop' {E A B} (f : A -> itree E A + B) (x : A) :
  observing eq
    (ITree.aloop f x)
    (ITree._aloop (fun t => Tau t) (ITree.aloop f) (f x)).
Proof.
  constructor; reflexivity.
Qed.

Lemma unfold_forever {E R S} (t: itree E R):
  observing eq (@ITree.forever E R S t) (ITree.bind t (fun _ => Tau (ITree.forever t))).
Proof. econstructor. reflexivity. Qed.

(** ** [going]: Lift relations through [go]. *)

Inductive going {E R1 R2} (r : itree E R1 -> itree E R2 -> Prop)
          (ot1 : itree' E R1) (ot2 : itree' E R2) : Prop :=
| going_intros : r (go ot1) (go ot2) -> going r ot1 ot2.
Hint Constructors going.

Lemma observing_going {E R1 R2} (eq_ : itree' E R1 -> itree' E R2 -> Prop) ot1 ot2 :
  going (observing eq_) ot1 ot2 <-> eq_ ot1 ot2.
Proof.
  split; auto.
  intros [[]]; auto.
Qed.

Section going_relations.

Context {E : Type -> Type} {R : Type}.
Variable (eq_ : itree E R -> itree E R -> Prop).

Global Instance going_go : Proper (going eq_ ==> eq_) (@go E R).
Proof. intros ? ? []; auto. Qed.

Global Instance monotonic_going eq_' :
  subrelation eq_ eq_' ->
  subrelation (going eq_) (going eq_').
Proof. intros ? ? ? []; eauto. Qed.

Global Instance Equivalence_going :
  Equivalence eq_ -> Equivalence (going eq_).
Proof.
  intros []; constructor; cbv; eauto.
  - intros ? ? []; auto.
  - intros ? ? ? [] []; eauto.
Qed.

End going_relations.
