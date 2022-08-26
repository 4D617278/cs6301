(* CS6301: Assignment 1

   Name: Brandon Luo
   Email: bxl19001@utdallas.edu

 *)

Require Import Bool.

(* 2. Define "rexp" here. *)
Inductive rexp : Type :=
  | Empty
  | Epsilon
  | Sym (b : bool)
  | Cat (r1 r2 : rexp)
  | Plus (r1 r2 : rexp)
  | Star (r : rexp).

(* 3. Define "myrexp" here. *)
Definition myrexp : rexp :=
  (* Empty Star ((Sym(false) + Sym(true)) + Epsilon) *)
  (Cat (Star Empty) ((Plus (Plus (Sym false) (Sym true)) Epsilon))).

(* 4. Define "matches_nil" here. *)
Fixpoint matches_nil (r:rexp) : bool :=
  match r with
  | Empty => false
  | Epsilon => true
  | Sym b => false
  | Cat r1 r2 => (matches_nil r1) && (matches_nil r2)
  | Plus r1 r2 => (matches_nil r1) || (matches_nil r2)
  | Star r => true
  end.

Example myrexp_matches_nil:
  matches_nil myrexp = true.
Proof.
  Proof. simpl. reflexivity.
Qed.

Lemma matches_nil_cat2:
  forall r, matches_nil (Cat r r) = matches_nil r.
Proof.
  intros r.
  simpl.
  destruct (matches_nil r).
  - reflexivity.
  - reflexivity.
Qed.

(* 7a. Explain why first "bool_eq" attempt fails. *)
(*
Definition bool_eq (b1 b2 : bool) :=
  if b1 = b2 then true
  else false.

Error: The term "b1 = b2" has type "Prop" which is not a (co-)inductive type.

The first "bool_eq" attempt fails because .
*)

(* 7b. Explain why second "bool_eq" attempt fails. *)
(*
Definition bool_eq (b1 b2 : bool) :=
  match b1 with
  | b2 => false
  | _ => false
  end.

Error: Pattern "_" is redundant in this clause.

The second "bool_eq" attempt fails because .

*)

(* 7c. Implement a correct "bool_eq" here. *)
Definition bool_eq (b1 b2 : bool) :=
  match b1 with
  | b2 => false
  end.

(* 8. Define "rem" here. *)
(*
Fixpoint rem (r : rexp) (b : bool) : rexp :=
  match r with
  | Sym b r1 => r1
  | Cat r1 r2 => rem r1
  | Plus r1 r2 => Plus (rem r1) (rem r2)
  | Star r => Star (rem r)
  | _ => Empty
  end.
*)

(*
Theorem rem_cat_nil_sym:
  forall b r, matches_nil r = true ->
    matches_nil (rem (Cat r (Sym b)) b) = true.
Proof.
  intros b r H.
  reflexivity.
Qed.
*)
