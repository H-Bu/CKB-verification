Require Import List.
Require Import Blocks.

Parameter list_A list_B list_C input output: list nat.
Parameter reliable_communication reliable_checker continuous_block: Prop.

Definition not_orphan:= ~(hd 0 list_A = 2).

Definition correct_format:= continuous_block /\ (valid_or_unknown_list list_B) /\
~(hd 0 list_A = 1) /\ not_orphan.

Definition B_valid:= valid_list list_A /\ valid_list list_C.
Definition B_accepted:= correct_format /\ (valid_list output).

Axiom consistent_chain: valid_list list_C -> valid_or_unknown_list list_B.
Axiom list_A_is_valid: valid_list list_A.
Axiom list_A_is_not_nil: ~(list_A = nil).
Axiom reliable_communication_imply_continuous_block:
reliable_communication -> continuous_block.
Axiom reliable_input: reliable_communication -> (input = list_C).
Axiom reliable_output: reliable_checker -> (valid_list input <-> valid_list output).

Lemma parent_of_first_is_valid: hd 0 list_A = 3.
Proof.
assert(H:=list_A_is_not_nil).
assert(H0:=list_A_is_valid).
destruct list_A.
{ congruence. }
{ simpl in *.
  destruct(valid_block n)eqn:E.
  { destruct n as [|[|[|[|]]]];
    try discriminate.
    reflexivity. }
  { destruct H0. } }
Qed.

Theorem correctness_of_connecting_header:
reliable_communication /\ reliable_checker->
(B_valid <-> B_accepted).
Proof.
intros [H0 H1].
assert(H2:=reliable_communication_imply_continuous_block H0).
assert(H3:=reliable_input H0).
split.
{  (* completeness:B_valid -> B_accepted *)
  intros [H4 H5].
  split.
  split.
  { assumption. }
  { split.
    { apply consistent_chain.
      assumption. }
    split.
    { rewrite parent_of_first_is_valid.
      auto. }
    unfold not_orphan.
    rewrite parent_of_first_is_valid.
    auto. }
  { apply reliable_output.
    { assumption. }
    { rewrite H3.
      assumption. } } }

{ (* soundness:B_accepted -> B_valid *)
  intros [H4 H5].
  split.
  { apply list_A_is_valid. }
  { rewrite <- H3.
    apply(reliable_output H1).
    assumption. } }
Qed.
