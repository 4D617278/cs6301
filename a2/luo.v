(* CS6301: Assignment 2

   Name: Brandon Luo
   Email: bxl190001@utdallas.edu

 *)

(* 1. Define "bin" here. *)

(* 2. Define "incr" here. *)

(* 3. Define "bin_to_nat" here. *)

Theorem bin_to_nat_pres_incr:
  forall b, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  (* 4. Complete the proof. *)
Qed.

(* 5. Define "nat_to_bin" here. *)

Theorem bin_nat_inv:
  forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  (* 6. Complete the proof. *)
Qed.

(* 7. Explain why (nat_to_bin (bin_to_nat b)) = b is not a true theorem. *)

(* 8. Define "normalize" here. *)

Theorem nat_bin_inv:
  forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  (* 9. Complete the proof. *)
Qed.
