Require Import List.
Require Import Blocks.

Parameter list_0 list_A list_B list_C list_D: list nat.
Parameter reliable_implement reliable_checker algorithm_termination: Prop.

Definition ACCEPT:= list_D=nil.
Definition REJECT:= ~list_D=nil /\ hd 0 list_D = 1.
Definition TIMEOUT:= ~list_D=nil /\ hd 0 list_D = 2.
Definition B_valid:= valid_list list_0.
Definition B_accepted:= ACCEPT.

Axiom reliable_listCD: reliable_implement -> valid_list list_C /\
(list_D = nil \/ ~(hd 0 list_D = 3)).
Axiom reliable_listAC: reliable_checker -> list_A = list_C.
Axiom one_of_three: algorithm_termination -> (ACCEPT /\ ~TIMEOUT /\ ~REJECT) \/
(~ACCEPT /\ TIMEOUT /\ ~REJECT) \/ (~ACCEPT /\ ~TIMEOUT /\ REJECT).
Axiom consistent_list0AB: (list_0 = list_A <-> list_B = nil) /\
(valid_list list_0 <-> valid_list list_A /\ valid_list list_B).
Axiom consistent_listBD: (list_D=nil -> list_B = nil) /\ (~list_D = nil -> ~list_B = nil) /\
((~list_B = nil /\ ~list_D = nil) -> ((hd 0 list_D = 2 -> (hd 0 list_B = 1 \/ hd 0 list_B = 3)) /\
(hd 0 list_D = 1 -> hd 0 list_B = 1))).

Lemma lemma_list2: valid_list list_B -> (hd 0 list_B = 3 \/ list_B = nil).
Proof.
intro.
destruct list_B.
{ auto. }
{ left.
  simpl in *.
  destruct(valid_block n)eqn:E.
  { destruct n as [|[|[|[|]]]];
    try discriminate.
    reflexivity. }
  { destruct H. } }
Qed.

Theorem soundness_of_downloading_block: reliable_checker /\ reliable_implement
-> (B_accepted -> B_valid).
Proof.
intros [H0 H1] H2.
assert(H3:list_D = nil).
{ auto. }
assert(H4:list_B = nil).
{ apply consistent_listBD.
  assumption. }
assert(H5:list_0 = list_A).
{ apply consistent_list0AB.
  assumption. }
assert(H6:=reliable_listAC H0).
assert(H7:valid_list list_C).
{ apply reliable_listCD.
  assumption. }
unfold B_valid.
congruence.
Qed.

Theorem completeness_of_downloading_block:reliable_checker /\ reliable_implement
/\ algorithm_termination /\ ~TIMEOUT -> (B_valid -> B_accepted).
Proof.
intros [H0 [H1 [H2 H3]]] H4.
assert(H5:=one_of_three H2).
destruct H5 as [H|[H|H]];
try tauto.
destruct H as [_ [_ [H5 H6]]].
assert(H7:hd 0 list_B = 1).
{ apply consistent_listBD.
  { split.
    { apply consistent_listBD.
      assumption. }
    { assumption. } }
  { assumption. } }
unfold B_valid in H4.
assert(H8:valid_list list_B).
{ apply consistent_list0AB.
  assumption. }
destruct(lemma_list2 H8).
{ congruence. }
{ assert(H9:~list_B = nil).
  { apply consistent_listBD.
    assumption. }
  contradiction. }
Qed.
