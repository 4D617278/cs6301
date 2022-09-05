(* CS6301: Assignment 2

   Name: Brandon Luo
   Email: bxl190001@utdallas.edu

 *)

(* 1. Define "bin" here. *)
Inductive bin : Type :=
  | Z
  | B0 (b : bin)
  | B1 (b : bin).

(* 2. Define "incr" here. *)
Fixpoint incr (b : bin) : bin :=
  match b with
  | Z => B1 Z
  | B0 B => B1 B
  | B1 B => B0 (incr B)
  end.

(* 3. Define "bin_to_nat" here. *)
Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | Z => 0
  | B0 B => 2 * (bin_to_nat B)
  | B1 B => 2 * (bin_to_nat B) + 1
  end.

Theorem add_0_r : forall n, n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. 
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. 
    rewrite -> add_0_r.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. 
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem bin_to_nat_pres_incr:
  forall b, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  induction b as [| b' IHb1' | b' IHb2'].
  - simpl. reflexivity.
  - simpl. 
  rewrite !add_0_r.
  rewrite add_comm.
  reflexivity.
  - simpl. 
  rewrite !add_0_r.
  rewrite IHb2'.
  simpl.
  replace (S (bin_to_nat b')) with (bin_to_nat b' + 1).
  + rewrite add_assoc. reflexivity.
  + rewrite add_comm. reflexivity.
Qed.

(* 5. Define "nat_to_bin" here. *)
Fixpoint nat_to_bin (n:nat) : bin :=
   match n with
   | O => Z
   | S n' => incr (nat_to_bin n')
   end.

Theorem bin_nat_inv:
  forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  simpl.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
  rewrite bin_to_nat_pres_incr.
  rewrite IHn'.
  reflexivity.
Qed.

(* 7. Explain why (nat_to_bin (bin_to_nat b)) = b is not a true theorem. *)
(* 
   bin_to_nat b' B0* Z = bin_to_nat b' Z

   nat_to_bin (bin_to_nat b' B0* Z) = nat_to_bin (bin_to_nat b' Z)

   b' B0* Z = b' Z 	(nat_to_bin (bin_to_nat b) = b)
   
   contradiction.
*)

(* 8. Define "normalize" here. *)
Definition double_bin (b:bin) : bin :=
  match b with
  | Z => Z
  | b' => B0 b'
  end.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  induction b as [| b' IHb' | b2' IHb2'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => double_bin (normalize b')
  | B1 b' => incr (double_bin (normalize b'))
  end.

Lemma nat_to_bin_incr : forall n,
  incr (nat_to_bin n) = nat_to_bin (n + 1).
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Lemma nat_to_bin_double_incr : forall n,
  incr (nat_to_bin (2 * n)) = nat_to_bin (2 * n + 1).
Proof.
  intros n.
  rewrite nat_to_bin_incr.
  reflexivity.
Qed.

Lemma double_bin_to_nat : forall b, bin_to_nat b + bin_to_nat b = 2 * bin_to_nat b.
Proof.
  intros b.
  simpl. 
  rewrite add_0_r. 
  reflexivity.
Qed.

Lemma double_nat_to_bin : forall n, nat_to_bin (2 * n) = double_bin (nat_to_bin n).
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. 
  rewrite add_0_r.
  rewrite double_incr_bin.
  rewrite <- IHn'.
  rewrite nat_to_bin_double_incr.
  simpl.
  rewrite add_0_r.
  rewrite <- add_assoc.
  replace (n' + 1) with (1 + n').
  + simpl. reflexivity.
  + rewrite add_comm. reflexivity.
Qed.

Theorem nat_bin_inv:
  forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b as [| b1' IHb1' | b2' IHb2'].
  - simpl. reflexivity.
  - simpl. 
  rewrite add_0_r.
  rewrite double_bin_to_nat.
  rewrite double_nat_to_bin.
  rewrite IHb1'. 
  reflexivity.
  - simpl. 
  rewrite add_0_r.
  rewrite double_bin_to_nat.
  rewrite <- nat_to_bin_double_incr.
  rewrite double_nat_to_bin.
  rewrite IHb2'.
  reflexivity.
Qed.
