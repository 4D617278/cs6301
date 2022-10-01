(* CS6301: Assignment 3

   Name: Brandon Luo
   Email: bxl190001@utdallas.edu

 *)

Require Import Bool.
Require Import List.

Inductive rexp {S : Set} : Type :=
  | Empty
  | Epsilon
  | Sym (A : S)
  | Cat (r1 r2 : rexp)
  | Plus (r1 r2 : rexp)
  | Star (r : rexp).

Definition myrexp : rexp :=
  (* Empty Star ((Sym(false) + Sym(true)) + Epsilon) *)
  (Cat (Star Empty) ((Plus (Plus (Sym false) (Sym true)) Epsilon))).

Fixpoint matches_nil {A : Set} (r : @rexp A) : bool :=
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
  forall r, @matches_nil bool (Cat r r) = @matches_nil bool r.
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

Definition eqdec (A : Set) := forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}.

Fixpoint rem {A : Set} (eq : eqdec A) (r : rexp) (b : bool) : rexp :=
  match r with
  | Empty => Empty
  | Epsilon => Empty
  | Sym b1 => if (bool_eq b1 b) then Epsilon else Empty
  | Cat r1 r2 => match (matches_nil r1) with
		 | true => Plus (rem eq r2 b) (Cat (rem eq r1 b) r2) 
		 | false => Cat (rem eq r1 b) r2
		 end
  | Plus r1 r2 => Plus (rem eq r1 b) (rem eq r2 b)
  | Star r => Cat (rem eq r b) (Star r)
  end.

Theorem rem_cat_nil_sym:
  forall b r eq, matches_nil r = true ->
    matches_nil (@rem bool eq (Cat r (Sym b)) b) = true.
Proof.
  intros b r eq H.
  simpl.
  rewrite -> H.
  rewrite b1_eq_b2.
  rewrite eqb_reflx.
  reflexivity.
Qed.

(* 1. Define "matches" here. *)
Fixpoint matches {A : Set} (eq : eqdec A) (r : rexp) (s : list bool) : bool :=
  match s with
  | nil => matches_nil r
  | h :: t => matches eq (rem eq r h) t
  end.

Theorem matches_plus_or:
  forall s r1 r2 eq, 
  @matches bool eq (Plus r1 r2) s = @matches bool eq r1 s || @matches bool eq r2 s.  
Proof.
  induction s; intros.
  - reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.

Theorem matches_app:
  forall s1 s2 r1 r2 eq, 
  @matches bool eq r1 s1 = true -> @matches bool eq r2 s2 = true ->
  @matches bool eq (Cat r1 r2) (s1++s2) = true.
Proof.
  induction s1; intros.
  - destruct s2; simpl in *; rewrite H, ?matches_plus_or, H0, ?orb_true_r; reflexivity.
  - simpl. destruct (matches_nil r1); 
  rewrite ?matches_plus_or, IHs1, ?orb_true_r; (reflexivity || assumption).
Qed.
