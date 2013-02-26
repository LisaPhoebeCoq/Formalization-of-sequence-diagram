Require Import Classical.
Set Implicit Arguments.
Section SEQUENCES.
Variable A: Type.
Variable R: A -> A -> Prop.
Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
  intros. econstructor; eauto. constructor.
Qed.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

CoInductive infseq: A -> Prop :=
  | infseq_step: forall a b,
      R a b -> infseq b -> infseq a.

Definition irred (a: A) : Prop := forall b, ~(R a b).
End SEQUENCES.


  


