(* CS6301: Assignment 3

   Name: Brandon Luo
   Email: bxl190001@utdallas.edu

 *)

Require Import Bool.
Require Import List.

(*** INSERT ASSIGNMENT 1 SOLUTION HERE. ***)
Inductive rexp : Type :=
  | Empty
  | Epsilon
  | Sym (b : bool)
  | Cat (r1 r2 : rexp)
  | Plus (r1 r2 : rexp)
  | Star (r : rexp).

Definition myrexp : rexp :=
  (* Empty Star ((Sym(false) + Sym(true)) + Epsilon) *)
  (Cat (Star Empty) ((Plus (Plus (Sym false) (Sym true)) Epsilon))).

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

Definition bool_eq (b1 b2 : bool) :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true
  end.

Theorem b1_eq_b2 : forall b1 b2 : bool, 
  bool_eq b1 b2 = eqb b1 b2.
Proof.
  reflexivity.
Qed.

Fixpoint rem (r : rexp) (b : bool) : rexp :=
  match r with
  | Empty => Empty
  | Epsilon => Empty
  | Sym b1 => if (bool_eq b1 b) then Epsilon else Empty
  | Cat r1 r2 => match (matches_nil r1) with
		 | true => Plus (rem r2 b) (Cat (rem r1 b) r2) 
		 | false => Cat (rem r1 b) r2
		 end
  | Plus r1 r2 => Plus (rem r1 b) (rem r2 b)
  | Star r => Cat (rem r b) (Star r)
  end.

Theorem rem_cat_nil_sym:
  forall b r, matches_nil r = true ->
    matches_nil (rem (Cat r (Sym b)) b) = true.
Proof.
  intros b r H.
  simpl.
  rewrite -> H.
  rewrite b1_eq_b2.
  rewrite eqb_reflx.
  reflexivity.
Qed.

(* 1. Define "matches" here. *)
Fixpoint matches (r : rexp) (s : list bool) : bool :=
  match s with
  | nil => matches_nil r
  | h :: t => matches (rem r h) t
  end.

Theorem matches_plus_or:
  forall s r1 r2, matches (Plus r1 r2) s = matches r1 s || matches r2 s.  Proof.
  induction s; intros.
  - reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.

Theorem matches_app:
  forall s1 s2 r1 r2, matches r1 s1 = true -> matches r2 s2 = true ->
    matches (Cat r1 r2) (s1++s2) = true.
Proof.
  induction s1; intros.
  - destruct s2; intros.
  + simpl.
  unfold matches in H. 
  unfold matches in H0.
  rewrite H.
  rewrite H0.
  reflexivity.
  + simpl. 
  unfold matches in H.
  rewrite H.
  simpl.
  rewrite matches_plus_or.
  simpl in H0.
  rewrite H0.
  reflexivity.
  - simpl. 
  destruct (matches_nil r1).
  + simpl. 
  rewrite matches_plus_or. 
  specialize IHs1 with (r1 := (rem r1 a)).
  specialize IHs1 with (r2 := r2).
  specialize IHs1 with (s2 := s2).
  rewrite IHs1.
  rewrite orb_true_r.
  reflexivity.
  simpl in H.
  rewrite H.
  reflexivity.
  rewrite H0.
  reflexivity.
  + specialize IHs1 with (r1 := (rem r1 a)).
  specialize IHs1 with (r2 := r2).
  specialize IHs1 with (s2 := s2).
  rewrite IHs1.
  reflexivity.
  simpl in H.
  rewrite H.
  reflexivity.
  rewrite H0.
  reflexivity.
Qed.
