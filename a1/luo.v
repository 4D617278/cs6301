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
Definition matches_nil (r:rexp) : bool :=
  match r with
  | Empty => false
  | Epsilon => true
  | Sym b => false
  | Cat r1 r2 => 
  | Plus r1 r2 => (matches_nil r1) && (matches_nil r2)
  | Star r => true
  | _ => false
  end.

Example myrexp_matches_nil:
  matches_nil myrexp = true.
Proof.
  (* 5. Complete the proof. *)
Qed.

Lemma matches_nil_cat2:
  forall r, matches_nil (Cat r r) = matches_nil r.
Proof.
  (* 6. Complete the proof. *)
Qed.

(* 7a. Explain why first "bool_eq" attempt fails. *)

(* 7b. Explain why second "bool_eq" attempt fails. *)

(* 7c. Implement a correct "bool_eq" here. *)

(* 8. Define "rem" here. *)

Theorem rem_cat_nil_sym:
  forall b r, matches_nil r = true ->
    matches_nil (rem (Cat r (Sym b)) b) = true.
Proof.
  (* 9. Complete the proof. *)
Qed.
