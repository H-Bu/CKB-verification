Require Import Sets.Ensembles.
Require Import Lia.

Parameter L: Ensemble nat.
Parameter B init: nat.
Parameter REJECT_ALL ACCEPT_B ACCEPT_OTHER: Prop.
Parameter reliable_checker: Prop.

Definition max_num(n: nat)(E: Ensemble nat):= E n /\ forall x, (E x /\ ~x = n -> x < n).

Axiom correct_implement: reliable_checker -> (REJECT_ALL <-> forall x, L x -> x <= init) /\
(ACCEPT_B <-> L B /\ B > init /\ forall x, (L x /\ ~x = B -> x < B)) /\
(ACCEPT_OTHER <-> exists x, (L x /\ ~x = B /\ x > init /\ forall y, (L y /\ ~x = y) -> y < x)).
Axiom B_is_max_in_L: max_num B L.

Theorem reject_other: reliable_checker -> ~ACCEPT_OTHER.
Proof.
intros H H0.
destruct(correct_implement H) as [_ [_ [H1 _]]].
destruct(H1 H0) as [x [H2 [H3 [H4 H5]]]];clear H1.
specialize H5 with B.
destruct(B_is_max_in_L) as [H6 H7].
specialize H7 with x.
assert(H8:B<x);auto.
assert(H9:x<B);auto.
lia.
Qed.

Theorem correctness_of_accepting_block: reliable_checker -> (init >= B -> REJECT_ALL)
/\ (init < B -> ACCEPT_B).
Proof.
intro.
destruct(correct_implement H) as [H0 [H1 _]].
split.
{ intro.
  rewrite H0;clear H0 H1.
  intros.
  assert(H1:x = B \/ ~x = B).
  { lia. }
  destruct H1.
  { rewrite H1.
    assumption. }
  { assert(H3:L x /\ ~x = B -> x < B).
    { apply B_is_max_in_L. }
    assert(H4:x<B);auto.
    lia. } }
{ rewrite H1;clear H0 H1.
  intro.
  split.
  { apply B_is_max_in_L. }
  split.
  { assumption. }
  { intros.
    apply B_is_max_in_L.
    assumption. } }
Qed.
