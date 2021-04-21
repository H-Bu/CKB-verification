Require Import List.

(* 1:invalid 2:unknown 3:valid *)

Definition valid_block(n: nat):=
  match n with
    | 3 => true
    | _ => false
  end.

Definition valid_or_unknown_block(n: nat):=
  match n with
    | 1 => false
    | _ => true
  end.

Fixpoint valid_list(l: list nat):=
  match l with
    | nil => True
    | a::m => if valid_block(a) then valid_list(m) else False
  end.

Fixpoint valid_or_unknown_list(l: list nat):=
  match l with
    | nil => True
    | a::m => if valid_or_unknown_block(a) then valid_or_unknown_list(m) else False
  end.