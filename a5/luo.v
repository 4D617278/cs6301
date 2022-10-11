(* CS6301: Assignment 5

   Name: Brandon Luo
   Email: bxl190001@utdallas.edu

 *)

Require Import List.
Print Forall.

Theorem Forall_app:
  forall (A:Type) P (l1 l2:list A),
    Forall P (l1++l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  intros A P l1 l2.
  split.
  - intros H. split.
  + induction l1; intros. 
    apply Forall_nil.
    simpl. apply Forall_cons. apply Forall_inv with (l := l1 ++ l2). apply H.
    simpl in *. apply IHl1. apply Forall_inv_tail with (a := a). apply H.
  + induction l1; intros.
    simpl in *. apply H.
    simpl in *. apply IHl1. apply Forall_inv_tail with (a := a). apply H.
  - intros H. destruct H. induction l1; intros; simpl.
  + apply H0. 
  + apply Forall_cons with (l := l1 ++ l2). 
    apply Forall_inv in H. apply H.
    apply IHl1. apply Forall_inv_tail in H. apply H.
Qed.

Theorem Forall_map:
  forall (A B:Type) P (f:A->B) l,
    Forall (fun x => P (f x)) l <-> Forall P (map f l).
Proof.
  induction l; intros.
  - simpl. rewrite Forall_nil_iff. rewrite Forall_nil_iff. reflexivity.
  - simpl in *. rewrite Forall_cons_iff. rewrite IHl. rewrite <- Forall_cons_iff. reflexivity.
Qed.

Theorem Forall_noadd:
  forall (A:Type) P f (l:list A),
    (forall x, In x (f l) -> In x l) -> Forall P l -> Forall P (f l).
Proof.
  intros A P f l H H2.
  rewrite Forall_forall.
  intros x H3.
  rewrite Forall_forall in H2.
  apply H2 with (x := x) in H.
  apply H.
  apply H3.
Qed.

Corollary Forall_rev:
  forall (A:Type) P (l:list A), Forall P (rev l) <-> Forall P l.
Proof.
  intros A P l.
  split.
  - intros H. apply Forall_rev in H. rewrite rev_involutive in H. apply H.
  - apply Forall_rev. 
Qed.
