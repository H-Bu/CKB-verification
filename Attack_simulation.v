Require Import List.
Require Import Blocks.

Parameter list_A list_C input output: list nat.
Parameter reliable_communication reliable_checker continuous_block: Prop.

Definition consistent_chain(l m: list nat):=
valid_list l -> valid_or_unknown_list m.

Definition not_orphan:= ~(hd 0 list_A = 2).

Definition correct_format(l: list nat):= continuous_block /\ (valid_or_unknown_list l) /\
~(hd 0 list_A = 1) /\ not_orphan.

Definition B_valid:= valid_list list_A /\ valid_list list_C.
Definition B_accepted(l: list nat):= correct_format l /\ (valid_list output).

Axiom list_A_is_valid: valid_list list_A.
Axiom list_A_is_not_nil: ~(list_A = nil).
Axiom reliable_communication_imply_continuous_block:
reliable_communication -> continuous_block.
Axiom reliable_input: reliable_communication -> (input = list_C).
Axiom reliable_output: reliable_checker -> (valid_list input <-> valid_list output).

Lemma exist_invalid_list: exists l: list nat, ~valid_or_unknown_list l.
Proof.
exists(1::nil).
auto.
Qed.

Theorem error_without_consistent_between_listBC:
reliable_communication /\ reliable_checker ->
exists list_B, (B_valid -> ~(B_accepted list_B)).
Proof.
intros.
destruct exist_invalid_list.
exists x.
intro.
assert(~correct_format x).
{ unfold correct_format.
  tauto. }
unfold B_accepted.
tauto.
Qed.
