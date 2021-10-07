(* midterm-project.v *)
(* FPP 2021 - YSC3236 2021-2022, Sem1 *)


(* ********** *)

(* A study of polymorphic lists. *)

(* name:
   email address:
   date: 

   please upload one .v file and one .pdf file containing a project report

   desiderata:
   - the file should be readable, i.e., properly indented and using items or {...} for subgoals
   - each use of a tactic should achieve one proof step
   - all lemmas should be applied to all their arguments
   - there should be no occurrences of admit, admitted, and abort
*)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Notation "A =n= B" :=
  (Nat.eqb A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (Bool.eqb A B) (at level 70, right associativity).

(* ********** *)

Definition eqb_option (V : Type) (eqb_V : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
  | Some v1 =>
    match ov2 with
    | Some v2 =>
      eqb_V v1 v2
    | None =>
      false
    end
  | None =>
    match ov2 with
    | Some v2 =>
      false
    | None =>
      true
    end
  end.

Notation "A =on= B" :=
  (eqb_option nat Nat.eqb A B) (at level 70, right associativity).

(* ********** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

Lemma fold_unfold_eqb_list_nil :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v2s : list V),
    eqb_list V eqb_V nil v2s =
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

Lemma fold_unfold_eqb_list_cons :
  forall (V : Type)
         (eqb_V : V -> V -> bool)
         (v1 : V)
         (v1s' v2s : list V),
    eqb_list V eqb_V (v1 :: v1s') v2s =
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end.
Proof.
  fold_unfold_tactic eqb_list.
Qed.

(* Task 1: *)
(* Proof by induction *)
Theorem soundness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        eqb_V v1 v2 = true -> v1 = v2) ->
    forall v1s v2s : list V,
      eqb_list V eqb_V v1s v2s = true ->
      v1s = v2s.
Proof.
  intros V eqb_V C_eqb_V v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - intros [ | v2 v2s'] H_eqb.
    -- reflexivity.
    -- rewrite -> (fold_unfold_eqb_list_nil V eqb_V (v2 :: v2s')) in H_eqb.
       discriminate H_eqb.
  - intros [ | v2 v2s'] H_eqb.
    -- rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' nil) in H_eqb.
       discriminate H_eqb.
    -- rewrite -> (fold_unfold_eqb_list_cons V eqb_V v1 v1s' (v2 :: v2s')) in H_eqb.
       Search (_ && _ = true -> _ /\ _).
       (* andb_prop: forall a b : bool, a && b = true -> a = true /\ b = true *)
       destruct (andb_prop (eqb_V v1 v2) (eqb_list V eqb_V v1s' v2s') H_eqb) as [H_eqb_1 H_eqb_2].
       rewrite -> (IHv1s' v2s' H_eqb_2).
       rewrite -> (C_eqb_V v1 v2 H_eqb_1).
       reflexivity.
Qed.

(* Proof by induction *)
Theorem completeness_of_equality_over_lists :
  forall (V : Type)
         (eqb_V : V -> V -> bool),
    (forall v1 v2 : V,
        v1 = v2 -> eqb_V v1 v2 = true) ->
    forall v1s v2s : list V,
      v1s = v2s ->
      eqb_list V eqb_V v1s v2s = true.
Proof.
  intros V eqb_V C_eqb v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - intros [ | v2 v2s'] H_eq.
    -- exact (fold_unfold_eqb_list_nil V eqb_V nil).
    -- discriminate H_eq.
  - intros [ | v2 v2s'] H_eq.
    -- discriminate H_eq.
    -- rewrite (fold_unfold_eqb_list_cons V eqb_V v1 v1s' (v2 :: v2s')).
       injection H_eq as H_eq_1 H_eq_2.
       rewrite -> (C_eqb v1 v2 H_eq_1).
       rewrite -> (IHv1s' v2s' H_eq_2).
       unfold andb.
       reflexivity.
Qed.

(* this proof requires light of inductil *)

(* ********** *)

(* A study of the polymorphic length function: *)

Definition specification_of_length (length : forall V : Type, list V -> nat) :=
  (forall V : Type,
      length V nil = 0)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     length V (v :: vs') = S (length V vs')).

(* Unit-test function: *)

Definition test_length (candidate : forall V : Type, list V -> nat) :=
  (candidate nat nil =n= 0) &&
  (candidate bool nil =n= 0) &&
  (candidate nat (1 :: nil) =n= 1) &&
  (candidate bool (true :: nil) =n= 1) &&
  (candidate nat (2 :: 1 :: nil) =n= 2) &&
  (candidate bool (false :: true :: nil) =n= 2) &&
  (candidate nat (3 :: 2 :: 1 :: nil) =n= 3) &&
  (candidate nat (3 :: 2 :: nil) =n= 2) &&
  (candidate nat (3 :: nil) =n= 1) &&
  (candidate bool (false :: false :: true :: nil) =n= 3).

(* The specification specifies at most one length function: *)

(* Proof by induction *)
Theorem there_is_at_most_one_length_function :
  forall (V : Type)
         (length_1 length_2 : forall V : Type, list V -> nat),
    specification_of_length length_1 ->
    specification_of_length length_2 ->
    forall vs : list V,
      length_1 V vs = length_2 V vs.
Proof.
  intros V length_1 length_2.
  unfold specification_of_length.
  intros [S_length_1_nil S_length_1_cons]
         [S_length_2_nil S_length_2_cons]
         vs.
  induction vs as [ | v vs' IHvs'].

  - Check (S_length_2_nil V).
    rewrite -> (S_length_2_nil V).
    Check (S_length_1_nil V).
    exact (S_length_1_nil V).

  - Check (S_length_1_cons V v vs').
    rewrite -> (S_length_1_cons V v vs').
    rewrite -> (S_length_2_cons V v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* The length function in direct style: *)

Fixpoint length_v0 (V : Type) (vs : list V) : nat :=
  match vs with
    | nil =>
      0
    | v :: vs' =>
      S (length_v0 V vs')
  end.

Compute (test_length length_v0).

(* Associated fold-unfold lemmas: *)

Lemma fold_unfold_length_v0_nil :
  forall V : Type,
    length_v0 V nil =
    0.
Proof.
  fold_unfold_tactic length_v0.
Qed.

Lemma fold_unfold_length_v0_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    length_v0 V (v :: vs') =
    S (length_v0 V vs').
Proof.
  fold_unfold_tactic length_v0.
Qed.

(* The specification specifies at least one length function: *)

Theorem length_v0_satisfies_the_specification_of_length :
  specification_of_length length_v0.
Proof.
  unfold specification_of_length.
  split.
  - exact fold_unfold_length_v0_nil.
  - exact fold_unfold_length_v0_cons.
Qed.

(* ***** *)

(* Task 2: *)

(* Implement the length function using an accumulator. *)

Fixpoint length_v1_aux (a : nat) (V : Type) (vs : list V) : nat  :=
  match vs with
    | nil =>
      a
    | v :: vs' =>
      length_v1_aux (S a) V vs' 
  end.

Definition length_v1 (V : Type) (vs : list V) : nat :=
  length_v1_aux 0 V vs .

Compute (test_length length_v1).

Lemma fold_unfold_length_v1_aux_nil :
  forall (V : Type)
         (a: nat),
    length_v1_aux a V nil =
    a.
Proof.
  fold_unfold_tactic length_v1_aux.
Qed.

Lemma fold_unfold_length_v1_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (a: nat),
    length_v1_aux a V (v :: vs')  =
    length_v1_aux (S a) V vs'.
Proof.
  fold_unfold_tactic length_v1_aux.
Qed.

(* prove that length_v1 satisfies the specification *)

Lemma about_length_v1_aux :
  forall (V : Type)
         (vs : list V)
         (a: nat),
    length_v1_aux (S a) V vs  =
    S (length_v1_aux a V vs).
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_length_v1_aux_nil V (S a)).
    rewrite -> (fold_unfold_length_v1_aux_nil V a).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' a).
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' (S a)).
    exact (IHvs' (S a)).
Qed.

(* this proof requires light of inductil *)

Theorem length_v1_aux_O_satisfies_the_specification_of_length :
    specification_of_length (length_v1_aux 0).
Proof.
  unfold specification_of_length.
  split.
  - intro V.
    exact (fold_unfold_length_v1_aux_nil V 0).
  - intros V v vs'.
    rewrite -> (fold_unfold_length_v1_aux_cons V v vs' 0).
    exact (about_length_v1_aux V vs' 0).
Qed.

Corollary length_v1_satisfies_the_specification_of_length :
  specification_of_length length_v1.
Proof.
  unfold length_v1.
  exact (length_v1_aux_O_satisfies_the_specification_of_length).
Qed.
  
(* ********** *)

(* A study of the polymorphic, left-to-right indexing function: *)

(* ***** *)

(* The indexing function can be specified by induction over the given list: *)

Definition test_list_nth (candidate : forall V : Type, list V -> nat -> option V) :=
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 0) =on= (Some 0)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 1) =on= (Some 1)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 2) =on= (Some 2)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 3) =on= (Some 3)) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 4) =on= None) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 5) =on= None) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 6) =on= None) &&
  ((candidate nat (0 :: 1 :: 2 :: 3 :: nil) 7) =on= None).

Fixpoint list_nth (V : Type) (vs : list V) (n : nat) : option V :=
  match vs with
  | nil =>
    None
  | v :: vs' =>
    match n with
    | O =>
      Some v
    | S n' =>
      list_nth V vs' n'
    end
  end.

Compute (test_list_nth list_nth).

Lemma fold_unfold_list_nth_nil :
  forall (V : Type)
         (n : nat),
    list_nth V nil n =
    None.
Proof.
  fold_unfold_tactic list_nth.
Qed.

Lemma fold_unfold_list_nth_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V)
         (n : nat),
    list_nth V (v :: vs') n =
    match n with
    | O =>
      Some v
    | S n' =>
      list_nth V vs' n'
    end.
Proof.
  fold_unfold_tactic list_nth.
Qed.

(* ***** *)

(* The indexing function can be specified by induction over the given index: *)

Definition test_nat_nth (candidate : forall V : Type, nat -> list V -> option V) :=
  ((candidate nat 0 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 0)) &&
  ((candidate nat 1 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 1)) &&
  ((candidate nat 2 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 2)) &&
  ((candidate nat 3 (0 :: 1 :: 2 :: 3 :: nil)) =on= (Some 3)) &&
  ((candidate nat 4 (0 :: 1 :: 2 :: 3 :: nil)) =on= None) &&
  ((candidate nat 5 (0 :: 1 :: 2 :: 3 :: nil)) =on= None) &&
  ((candidate nat 6 (0 :: 1 :: 2 :: 3 :: nil)) =on= None) &&
  ((candidate nat 7 (0 :: 1 :: 2 :: 3 :: nil)) =on= None).

Fixpoint nat_nth (V : Type) (n : nat) (vs : list V) : option V :=
  match n with
  | O =>
    match vs with
    | nil =>
      None
    | v :: vs' =>
      Some v
    end
  | S n' =>
    match vs with
    | nil =>
      None
    | v :: vs' =>
      nat_nth V n' vs'
    end
  end.

Compute (test_nat_nth nat_nth).

Lemma fold_unfold_nat_nth_O :
  forall (V : Type)
         (vs : list V),
    nat_nth V O vs =
    match vs with
    | nil =>
      None
    | v :: vs' =>
      Some v
    end.
Proof.
  fold_unfold_tactic nat_nth.
Qed.

Lemma fold_unfold_nat_nth_S :
  forall (V : Type)
         (n' : nat)
         (vs : list V),
    nat_nth V (S n') vs =
    match vs with
    | nil =>
      None
    | v :: vs' =>
      nat_nth V n' vs'
    end.
Proof.
  fold_unfold_tactic nat_nth.
Qed.

(* ***** *)

(* Task 3: *)

(*
   a. Both list-indexing functions come with their own unit-test function.
      Test each implementation with the unit-test function of the other implementation,
      and verify that it passes this other test.
*)

Definition list_nth_for_test_nat_nth (V : Type) (n : nat) (vs : list V) : option V :=
  list_nth V vs n.
  
Compute (test_nat_nth list_nth_for_test_nat_nth).
(* 
     = true
     : bool
 *)

Definition nat_nth_for_test_list_nth (V : Type) (vs : list V) (n : nat) : option V :=
  nat_nth V n vs.

Compute (test_list_nth nat_nth_for_test_list_nth).
(* 
     = true
     : bool
 *)

(*
   b. Prove by induction on natural numbers that if, given a list and an index, list_nth yields a result,
      then given this index and this list, nat_nth yields the same result
*)

(* Proof by induction *)
Proposition list_nth_implies_nat_nth :
  forall (V : Type)
         (vs : list V)
         (n : nat)
         (ov : option V),
    list_nth V vs n = ov ->
    nat_nth V n vs = ov.
Proof.
  (* proof by induction on natural number *)
  intros V vs n ov.
  revert vs.
  induction n as [ | n' IHn'].
  - destruct vs as [ | v vs'] eqn:H_vs.
    -- intro H_list_result.
       rewrite -> (fold_unfold_nat_nth_O V nil).
       rewrite -> (fold_unfold_list_nth_nil V 0) in H_list_result.
       exact (H_list_result).
    -- intro H_list_result.
       rewrite -> (fold_unfold_nat_nth_O V (v :: vs')).
       rewrite -> (fold_unfold_list_nth_cons V v vs' 0) in H_list_result.
       exact (H_list_result).
  - destruct vs as [ | v vs'] eqn:H_vs.
    -- intro H_list_result.
       rewrite -> (fold_unfold_nat_nth_S V n' nil).
       rewrite -> (fold_unfold_list_nth_nil V (S n')) in H_list_result.
       exact (H_list_result).
    -- intro H_list_result.
       rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) .
       rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')) in H_list_result.
       rewrite -> (IHn' vs' H_list_result).
       reflexivity.

  Restart.

  (* proof by induction on lists *)
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - destruct n as [ | n'].
    -- rewrite -> (fold_unfold_list_nth_nil V 0).
       rewrite -> (fold_unfold_nat_nth_O V nil).
       intros ov H_ov.
       exact H_ov.
    -- rewrite -> (fold_unfold_list_nth_nil V (S n')).
       rewrite -> (fold_unfold_nat_nth_S V n' nil).
       intros ov H_ov.
       exact H_ov.
  - destruct n as [ | n'].
    -- rewrite -> (fold_unfold_list_nth_cons V v vs' 0).
       rewrite -> (fold_unfold_nat_nth_O V (v :: vs')).
       intros ov H_ov.
       exact H_ov.
    -- rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
       rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')).
       exact (IHvs' n').
Qed.

(* this proof requires light of inductil *)

(* Could you prove this proposition by induction on lists? *)

(*
   c. Prove by induction on lists that if, given an index and a list, nat_nth yields a result,
      then given this list and this index, list_nth yields the same result
 *)

(* Proof by induction *)
Proposition nat_nth_implies_list_nth :
  forall (V : Type)
         (n : nat)
         (vs : list V)
         (ov : option V),
    nat_nth V n vs = ov ->
    list_nth V vs n = ov.
Proof.
  (* proof by induction on list *)
  intros V n vs ov.
  revert n.
  induction vs as [ | v vs' IHvs'].
  - destruct n as [ | n'] eqn: H_n.
    -- intro H_nat_result.
       rewrite -> (fold_unfold_nat_nth_O V nil) in H_nat_result.
       rewrite -> (fold_unfold_list_nth_nil V 0).
       exact (H_nat_result).
    -- intro H_nat_result.
       rewrite -> (fold_unfold_nat_nth_S V n' nil) in H_nat_result.
       rewrite -> (fold_unfold_list_nth_nil V (S n')).
       exact (H_nat_result).
  - destruct n as [ | n'] eqn: H_n.
    -- intro H_nat_result.
       rewrite -> (fold_unfold_nat_nth_O V (v :: vs')) in H_nat_result.
       rewrite -> (fold_unfold_list_nth_cons V v vs' 0).
       exact (H_nat_result).
    -- intro H_nat_result.
       rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) in H_nat_result.
       rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
       rewrite -> (IHvs' n' H_nat_result).
       reflexivity.

       Restart.

  (* proof by induction on natural number *)
  intros V n vs ov.
  revert vs.
  induction n as [ | n' IHn'].
  - destruct vs as [ | v vs'] eqn:H_vs.
    -- intro H_nat_result.
       rewrite -> (fold_unfold_nat_nth_O V nil) in H_nat_result.
       rewrite -> (fold_unfold_list_nth_nil V 0).
       exact (H_nat_result).
    -- intro H_nat_result.
       rewrite -> (fold_unfold_nat_nth_O V (v :: vs')) in H_nat_result.
       rewrite -> (fold_unfold_list_nth_cons V v vs' 0).
       exact (H_nat_result).
  - destruct vs as [ | v vs'] eqn:H_vs.
    -- intro H_nat_result.
       rewrite -> (fold_unfold_nat_nth_S V n' nil) in H_nat_result.
       rewrite -> (fold_unfold_list_nth_nil V (S n')).
       exact (H_nat_result).
    -- intro H_nat_result.
       rewrite -> (fold_unfold_nat_nth_S V n' (v :: vs')) in H_nat_result.
       rewrite -> (fold_unfold_list_nth_cons V v vs' (S n')).
       rewrite -> (IHn' vs' H_nat_result).
       reflexivity.      
Qed.

(* this proof requires light of inductil *)

(*
   d. What do you conclude?
      Swapping the argments is indeed all it takes to go from one specification to another.
*)

(* ********** *)

(* A study of the polymorphic copy function: *)

Definition specification_of_copy (copy : forall V : Type, list V -> list V) :=
  (forall V : Type,
      copy V nil = nil)
  /\
  (forall (V : Type)
          (v : V)
          (vs' : list V),
     copy V (v :: vs') = v :: (copy V vs')).

Definition test_copy (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat Nat.eqb (candidate nat nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (2 :: 1 :: nil)) (2 :: 1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil)) (false :: true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (3 :: 5 :: 2 :: 1 :: nil)) (3 :: 5 :: 2 :: 1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: false :: true :: false :: true :: nil))
            (false :: false :: true :: false :: true :: nil)).

(* Task 4:

   a. expand the unit-test function for copy with a few more tests

   b. implement the copy function in direct style
*)

Fixpoint copy_v0 (V : Type) (vs : list V) : list V :=
  match vs with
    | nil => nil
    | v :: vs' => v :: (copy_v0 V vs')
  end.

Compute (test_copy copy_v0).
(*
     = true
     : bool
*)

(*
   c. state its associated fold-unfold lemmas
*)

Lemma fold_unfold_copy_v0_nil :
  forall (V : Type),
    copy_v0 V nil = nil.
Proof.
  fold_unfold_tactic copy_v0.
Qed.
 
Lemma fold_unfold_copy_v0_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    copy_v0 V (v :: vs') = v :: (copy_v0 V vs').
Proof.
  fold_unfold_tactic copy_v0.
Qed.

(*
   d. prove whether your implementation satisfies the specification.
*)

Theorem copy_v0_satisfies_the_specification_of_copy :
  specification_of_copy copy_v0.
Proof.
  unfold specification_of_copy.
  split.
  - exact (fold_unfold_copy_v0_nil).
  - exact (fold_unfold_copy_v0_cons).
Qed.

(*
   e. prove whether copy is idempotent
*)


Proposition copy_is_idempotent :
  forall (V : Type)
         (vs : list V),
    copy_v0 V (copy_v0 V vs) = copy_v0 V vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - exact (fold_unfold_copy_v0_nil V).
  - rewrite -> (fold_unfold_copy_v0_cons V v vs').
    rewrite -> (fold_unfold_copy_v0_cons V v (copy_v0 V vs')).
    rewrite -> (IHvs').
    reflexivity.
Qed.

(*
   f. prove whether copying a list preserves its length
 *)

(* Proof by induction *)
Proposition copy_preserves_length :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (copy_v0 V vs) = n.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - intros n H_length.
    rewrite -> (fold_unfold_copy_v0_nil V).
    exact (H_length).
  - destruct n as [ | n'].
    -- intro H_length.
       rewrite -> (fold_unfold_length_v0_cons V v vs') in H_length.
       discriminate (H_length).
    -- intro H_length.
       rewrite -> (fold_unfold_copy_v0_cons V v vs').
       rewrite -> (fold_unfold_length_v0_cons V v (copy_v0 V vs')).
       rewrite -> (fold_unfold_length_v0_cons V v vs') in H_length.
       Search (S _ = S _).
       (* eq_add_S: forall n m : nat, S n = S m -> n = m *)
       apply eq_add_S in H_length.
       rewrite -> (IHvs' n' H_length).
       reflexivity.
Qed.

(* this proof requires light of inductil, as we destruct the n *)

(*
   G. subsidiary question: can you think of a strikingly simple implementation of the copy function?
      if so, pray show that it satisfies the specification of copy
*)

Definition copy_v1 (V : Type) (vs : list V) : list V :=
  vs.

Compute (test_copy copy_v1).
(* 
     = true
     : bool
*)

Theorem copy_v1_satisfies_the_specification_of_copy :
  specification_of_copy copy_v1.
Proof.
  unfold specification_of_copy.
  split.
  - intro V.
    unfold copy_v1.
    reflexivity.
  - intros V v vs'.
    unfold copy_v1.
    reflexivity.
Qed.

(* ********** *)

(* A study of the polymorphic append function: *)

Definition specification_of_append (append : forall V : Type, list V -> list V -> list V) :=
  (forall (V : Type)
          (v2s : list V),
      append V nil v2s = v2s)
  /\
  (forall (V : Type)
          (v1 : V)
          (v1s' v2s : list V),
      append V (v1 :: v1s') v2s = v1 :: append V v1s' v2s).

(* Task 5:

   a. define a unit-test function for append
*)

Definition test_append (candidate : forall V : Type, list V -> list V -> list V) : bool :=
  (eqb_list nat beq_nat (candidate nat (2 :: 1 :: nil) (1 :: 0 :: nil)) (2 :: 1 :: 1 :: 0 :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (9 :: 8 :: nil) (7 :: 6 :: nil)) (9 :: 8 :: 7 :: 6 :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (10 :: 11 :: nil) (12 :: 13 :: nil)) (10 :: 11 :: 12 :: 13 :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (2 :: nil) (1 :: 0 :: nil)) (2 :: 1 :: 0 :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (4 :: nil) (16 :: 9 :: nil)) (4 :: 16 :: 9 :: nil)) &&
  (eqb_list nat beq_nat (candidate nat (nil) (1 :: 0 :: nil)) (1 :: 0 :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat nil nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool nil nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: nil) nil) (1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: nil) nil) (true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (2 :: 1 :: nil) (4 :: nil)) (2 :: 1 :: 4 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil) (true :: true :: false :: nil))
            (false :: true :: true :: true :: false :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (3 :: 5 :: nil) (6 :: 7 :: 8 :: nil)) (3 :: 5 :: 6 :: 7 :: 8 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: nil )(false :: false :: true :: false :: true :: nil))
            (true :: false :: false :: true :: false :: true :: nil)).

(*
   b. implement the append function in direct style
*)

Fixpoint append_v0 (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
    | nil => v2s
    | v :: vs' => v :: (append_v0 V vs' v2s)
  end.

Compute test_append append_v0.
(* 
     = true
     : bool
*)

(* c. state its associated fold-unfold lemmas *)

Lemma fold_unfold_append_v0_nil :
  forall (V : Type)
         (v2s : list V),
    append_v0 V nil v2s = v2s.
Proof.
  fold_unfold_tactic append_v0.
Qed.

Lemma fold_unfold_append_v0_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    append_v0 V (v1 :: v1s') v2s = v1 :: (append_v0 V v1s' v2s).
Proof.
  fold_unfold_tactic append_v0.
Qed.

(*  d. prove that your implementation satisfies the specification *)

Theorem append_v0_satisfies_the_specification_of_append :
  specification_of_append append_v0.
Proof.
  unfold specification_of_append.
  split.
  - exact (fold_unfold_append_v0_nil).
  - exact (fold_unfold_append_v0_cons).
Qed.

(*  e. prove whether nil is neutral on the left of append *)

Theorem nil_is_neutral_on_append_v0_left :
  forall (V : Type)
         (vs : list V),
    append_v0 V nil vs = vs.
Proof.
  intros V vs.
  exact (fold_unfold_append_v0_nil V vs).
Qed.

(*  f. prove whether nil is neutral on the right of append *)

Theorem nil_is_neutral_on_append_v0_right :
  forall (V : Type)
         (vs : list V),
    append_v0 V vs nil = vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - exact (fold_unfold_append_v0_nil V nil).
  - rewrite -> (fold_unfold_append_v0_cons V v vs' nil).
    rewrite -> IHvs'.
    reflexivity.
Qed.

(* g. prove whether append is commutative *)

Theorem append_v0_is_not_commutative :
  exists (V : Type)
         (v1s v2s : list V),
    append_v0 V v1s v2s <> append_v0 V v2s v1s.
Proof.
  unfold not.
  exists (nat : Type).
  exists ((1 :: nil) : list nat).
  exists ((2 :: nil) : list nat).
  rewrite -> (fold_unfold_append_v0_cons nat 1 nil (2 :: nil)).
  rewrite -> (fold_unfold_append_v0_nil nat (2 :: nil)).
  rewrite -> (fold_unfold_append_v0_cons nat 2 nil (1 :: nil)).
  rewrite -> (fold_unfold_append_v0_nil nat (1 :: nil)).
  discriminate.
Qed.

(*  h. prove whether append is associative *)

(* Proof by induction *)
Theorem append_v0_is_associative :
  forall (V : Type)
         (v1s v2s v3s: list V),
    append_v0 V v1s (append_v0 V v2s v3s) = append_v0 V (append_v0 V v1s v2s) v3s.
Proof.
  intros V v1s v2s v3s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - rewrite -> (fold_unfold_append_v0_nil V (append_v0 V v2s v3s)).
    rewrite -> (fold_unfold_append_v0_nil V v2s).
    reflexivity.
  - rewrite -> (fold_unfold_append_v0_cons V v1 v1s' (append_v0 V v2s v3s)).
    rewrite -> IHv1s'.
    rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_append_v0_cons V v1 (append_v0 V v1s' v2s) v3s).
    reflexivity.
Qed.

(* this proof does not require the light of inductil *)

(* i. prove whether appending two lists preserves their length *)

(* Proof by induction *)
Proposition append_preserves_length :
  forall (V : Type)
         (v1s v2s : list V)
         (n1 n2 : nat),
    length_v0 V v1s = n1 ->
    length_v0 V v2s = n2 ->
    length_v0 V (append_v0 V v1s v2s) = n1 + n2.
Proof.
  intros V v1s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - intros v2s n1 n2  H_length_v1s H_length_v2s.
    rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_length_v0_nil V) in H_length_v1s.
    rewrite <- H_length_v1s.
    rewrite -> (Nat.add_0_l).
    exact (H_length_v2s).
  - intros v2s [ | n'] n2 H_length_v1s' H_length_v2s.
    -- discriminate H_length_v1s'.
    -- rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
       rewrite -> (fold_unfold_length_v0_cons V v1 (append_v0 V v1s' v2s)).
       rewrite -> (IHv1s' v2s n' n2).
       --- exact (Nat.add_succ_l n' n2).
       --- rewrite -> (fold_unfold_length_v0_cons V v1 v1s') in H_length_v1s'.
           rewrite -> (Nat.succ_inj (length_v0 V v1s') n' H_length_v1s').
           reflexivity.
       --- exact (H_length_v2s).
   (* In this proof, there is an assumption that is not met yet when we did "rewrite -> (IHv1s' v2s n' n2).", which adds to the subgoal. We can address this by using injection in the subgoal. *)

   Restart.
   intros V v1s.
   induction v1s as [ | v1 v1s' IHv1s'].
  - intros v2s n1 n2  H_length_v1s H_length_v2s.
    rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_length_v0_nil V) in H_length_v1s.
    rewrite <- H_length_v1s.
    rewrite -> (Nat.add_0_l).
    exact (H_length_v2s).
  - intros v2s [ | n'] n2 H_length_v1s' H_length_v2s.
    -- discriminate H_length_v1s'.
    -- rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
       rewrite -> (fold_unfold_length_v0_cons V v1 (append_v0 V v1s' v2s)).
       rewrite -> (fold_unfold_length_v0_cons V v1 v1s') in H_length_v1s'.
       injection H_length_v1s' as H_length_v1s'.
       rewrite -> (IHv1s' v2s n' n2 H_length_v1s' H_length_v2s).
       exact (Nat.add_succ_l n' n2).
Qed.

(* Both proofs require light of inductil *)

(* Proof by induction *)
Proposition append_preserves_length_alt :
  forall (V : Type)
         (v1s v2s : list V),
    length_v0 V (append_v0 V v1s v2s) = length_v0 V v1s + length_v0 V v2s.
Proof.
  intros V v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_length_v0_nil V).
    rewrite -> (Nat.add_0_l (length_v0 V v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_length_v0_cons V v1 (append_v0 V v1s' v2s)).
    rewrite -> IHv1s'.
    rewrite -> (fold_unfold_length_v0_cons V v1 v1s').
    exact (Nat.add_succ_l (length_v0 V v1s') (length_v0 V v2s)).
Qed.

(* this proof does not require light of inductil *)

(* j. prove whether append and copy commute with each other *)

(* Proof by induction *)
Proposition append_and_copy_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    copy_v0 V (append_v0 V v1s v2s) = append_v0 V (copy_v0 V v1s) (copy_v0 V v2s).
Proof.
  intros V v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_copy_v0_nil V).
    rewrite -> (fold_unfold_append_v0_nil V (copy_v0 V v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_copy_v0_cons V v1 (append_v0 V v1s' v2s)).
    rewrite -> IHv1s'.
    rewrite -> (fold_unfold_copy_v0_cons V v1 v1s').
    rewrite -> (fold_unfold_append_v0_cons V v1 (copy_v0 V v1s') (copy_v0 V v2s)).
    reflexivity.
Qed.

(* this proof does not require light of inductil *)

(* ********** *)

(* A study of the polymorphic reverse function: *)

Definition specification_of_reverse (reverse : forall V : Type, list V -> list V) :=
  forall append : forall W : Type, list W -> list W -> list W,
    specification_of_append append ->
    (forall V : Type,
        reverse V nil = nil)
    /\
    (forall (V : Type)
            (v : V)
            (vs' : list V),
        reverse V (v :: vs') = append V (reverse V vs') (v :: nil)).

(* Task 6:

   a. Define a unit-test function for an implementation of the reverse function.
*)

Definition test_reverse (candidate : forall V : Type, list V -> list V) :=
  (eqb_list nat beq_nat (candidate nat (2 :: 1 :: nil)) (1 :: 2 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat (1 :: nil)) (1 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat (2 :: 2 :: nil)) (2 :: 2 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat (2 :: 1 :: 9 :: nil)) (9 :: 1 :: 2 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat (4 :: 3 :: 2 :: 1 :: nil)) (1 :: 2 :: 3 :: 4 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat (11 :: 2 ::  nil)) (2 :: 11 :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat (1 :: nil)) (1 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (true :: nil)) (true :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (2 :: 1 :: nil)) (1 :: 2 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: true :: nil)) (true :: false ::  nil)) &&
  (eqb_list nat Nat.eqb (candidate nat (3 :: 5 :: 2 :: 1 :: nil)) (1 :: 2 :: 5 :: 3 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool (false :: false :: false :: true :: false :: true :: nil))
            (true :: false :: true :: false :: false :: false :: nil)).
(*
   b. Implement the reverse function recursively and in direct style, using append_v0.
*)

Fixpoint reverse_v0 (V : Type) (vs : list V) : list V :=
  match vs with
    | nil => nil
    | v :: vs' => append_v0 V (reverse_v0 V vs') (v :: nil)
  end.

Compute test_reverse reverse_v0.
(*
     = true
     : bool
*)

(*
   c. State the associated fold-unfold lemmas.
*)

Lemma fold_unfold_reverse_v0_nil :
  forall (V : Type),
    reverse_v0 V nil = nil.
Proof.
  fold_unfold_tactic reverse_v0.
Qed.

Lemma fold_unfold_reverse_v0_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    reverse_v0 V (v :: vs') = append_v0 V (reverse_v0 V vs') (v :: nil).
Proof.
  fold_unfold_tactic reverse_v0.
Qed.

(*
   d. Prove whether your implementation satisfies the specification.
*)

(* Proof by induction *)
Lemma equivalence_of_append :
  forall append: forall W : Type, list W -> list W -> list W,
    specification_of_append append ->
    forall (V : Type)
           (v1s v2s : list V),
    append_v0 V v1s v2s  = append V v1s v2s.
Proof.
  intros append [S_append_nil S_append_cons] V v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s'].
  - rewrite -> (S_append_nil V v2s).
    exact (fold_unfold_append_v0_nil V v2s).
  - rewrite -> (S_append_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
    rewrite -> IHv1s'.
    reflexivity.
Qed.

(* this proof does not require light of inductil *)

Theorem reverse_v0_satisfies_the_specification_of_reverse :
  specification_of_reverse reverse_v0.

Proof.
  unfold specification_of_reverse.
  intros append S_append.
  split.
  - exact (fold_unfold_reverse_v0_nil).
  - intros V v vs'.
    rewrite -> (fold_unfold_reverse_v0_cons V v vs').
    rewrite -> (equivalence_of_append append S_append V (reverse_v0 V vs') (v :: nil)).
    reflexivity.
Qed.

(*
   e. prove whether reverse_v0 is involutory.
*)

(* Proof by induction *)
Lemma about_reverse_v0 :
  forall (V : Type)
         (v : V)
         (vs : list V),
    reverse_v0 V (append_v0 V vs (v :: nil)) = v :: reverse_v0 V vs.
Proof.
  intros V v vs.
  induction vs as [ | v'' vs'' IHvs''].
  - rewrite -> (fold_unfold_append_v0_nil V (v :: nil)).
    rewrite -> (fold_unfold_reverse_v0_cons V v nil).
    rewrite -> (fold_unfold_reverse_v0_nil V).
    rewrite -> (fold_unfold_append_v0_nil V (v :: nil)).
    reflexivity.
  - rewrite -> (fold_unfold_append_v0_cons V v'' vs'' (v :: nil)).
    rewrite -> (fold_unfold_reverse_v0_cons V v'' vs'').
    rewrite -> (fold_unfold_reverse_v0_cons V v'' (append_v0 V vs'' (v :: nil))).
    rewrite -> (IHvs'').
    rewrite -> (fold_unfold_append_v0_cons V v (reverse_v0 V vs'') (v'' :: nil)).
    reflexivity.
Qed.

(* this proof does not require light of inductil *)

(* Proof by induction *)
Proposition reverse_v0_is_involutory :
  forall (V : Type)
         (vs : list V),
    reverse_v0 V (reverse_v0 V vs) = vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_cons V v vs').
    rewrite -> (about_reverse_v0 V v (reverse_v0 V vs')).
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   f. Prove whether reversing a list preserves its length.
*)

(* Proof by induction *)
Proposition reverse_v0_preserves_length :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (reverse_v0 V vs) = n.
Proof.
  intro V.
  induction vs as [ | v vs' IHvs'].
  - intros n H_length.
    rewrite -> (fold_unfold_reverse_v0_nil V).
    exact H_length.
  - intros [ | n'] H_length.
    -- discriminate H_length.
    -- rewrite -> (fold_unfold_reverse_v0_cons V v vs').
       rewrite -> (append_preserves_length_alt V (reverse_v0 V vs') (v :: nil)).
       rewrite -> (fold_unfold_length_v0_cons V v nil).
       rewrite -> (fold_unfold_length_v0_nil V).
       rewrite -> (fold_unfold_length_v0_cons V v vs') in H_length.
       injection H_length as H_length. 
       rewrite -> (IHvs' n' H_length).
       exact (Nat.add_1_r n').
Qed.

(* this proof requires light of inductil *)

(* Proof by induction *)
Proposition reverse_v0_preserves_length_alt :
  forall (V : Type)
         (vs : list V),
    length_v0 V (reverse_v0 V vs) = length_v0 V vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_nil V).
    reflexivity.
  - rewrite -> (fold_unfold_reverse_v0_cons V v vs').
    rewrite -> (append_preserves_length_alt V (reverse_v0 V vs') (v :: nil)).
    rewrite -> (fold_unfold_length_v0_cons V v nil).
    rewrite -> (fold_unfold_length_v0_nil V).
    rewrite -> (IHvs').
    rewrite -> (fold_unfold_length_v0_cons V v vs').
    exact (Nat.add_1_r (length_v0 V vs')).
Qed.

(* reverse_v0_preserves_length as a corollary of reverse_v0_preserves_length_alt *)

Corollary reverse_v0_preserves_length':
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (reverse_v0 V vs) = n.
Proof.
  intros V vs n H_length.
  rewrite -> (reverse_v0_preserves_length_alt V vs).
  exact (H_length).
Qed.

(* reverse_v0_preserves_length_alt as a corollary of reverse_v0_preserves_length *)

Corollary reverse_v0_preserves_length_alt' :
  forall (V : Type)
         (vs : list V),
    length_v0 V (reverse_v0 V vs) = length_v0 V vs.
Proof.
  intros V vs.
  apply (reverse_v0_preserves_length V vs (length_v0 V vs)).
  reflexivity.
Qed.

(*
   g. Do append_v0 and reverse_v0 commute with each other (hint: yes they do) and if so how?
*)

(* 
   brings back fond memories of commuting diagrams :')
*)

(* Proof by induction *)
Proposition append_and_reverse_v0_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v0 V (append_v0 V v1s v2s) = append_v0 V (reverse_v0 V v2s) (reverse_v0 V v1s).
Proof.
  intros V v1s v2s.
  induction v1s as [ | v1 v1s' IHv1s']. 
  - rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_reverse_v0_nil V).
    rewrite -> (nil_is_neutral_on_append_v0_right V (reverse_v0 V v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_reverse_v0_cons V v1 (append_v0 V v1s' v2s)).
    rewrite -> (IHv1s').
    rewrite -> (fold_unfold_reverse_v0_cons V v1 v1s').
    rewrite <- (append_v0_is_associative V (reverse_v0 V v2s) (reverse_v0 V v1s') (v1 :: nil)).
    reflexivity.
Qed.

(* this proof does not require light of inductil *)

(*
   h. Implement the reverse function using an accumulator instead of using append_v0.
*)

Fixpoint reverse_v1_aux (V : Type) (vs : list V) (a : list V) : list V :=
  match vs with
  | nil => a
  | v :: vs' => reverse_v1_aux V vs' (v :: a)
  end.

Definition reverse_v1 (V : Type) (vs : list V) : list V :=
  reverse_v1_aux V vs nil.

Compute test_reverse reverse_v1.
(*
     = true
     : bool
*)

Lemma fold_unfold_reverse_v1_aux_nil :
  forall (V : Type)
         (a : list V),
    reverse_v1_aux V nil a =
    a.
Proof.
  fold_unfold_tactic reverse_v1_aux.
Qed.

Lemma fold_unfold_reverse_v1_aux_cons :
  forall (V : Type)
         (v : V)
         (vs' a : list V),
    reverse_v1_aux V (v :: vs') a =
    reverse_v1_aux V vs' (v :: a).
Proof.
  fold_unfold_tactic reverse_v1_aux.
Qed.

(*
   i. Revisit the propositions above (involution, preservation of length, commutation with append)
      and prove whether reverse_v1 satisfies them.
      Two proof strategies are possible:
      (1) direct, stand-alone proofs with Eureka lemmas, and
      (2) proofs that hinge on the equivalence of reverse_v1 and reverse_v0.
      This subtask is optional.
 *)

(* Proof by induction *)
Lemma about_reverse_v1_aux :
  forall (V : Type)
         (vs a: list V),
    reverse_v1_aux V vs a = append_v0 V (reverse_v1_aux V vs nil) a.
Proof.
  intro V.
  induction vs as [ | v vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V a).
    rewrite -> (fold_unfold_reverse_v1_aux_nil V nil).
    rewrite -> (fold_unfold_append_v0_nil V a).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' a).
    rewrite -> (IHvs' (v :: a)).
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' nil).
    rewrite -> (IHvs' (v :: nil)).
    (* try to get the same number of append_v0 on each side of the goal, so that we can compare them *)
    rewrite <- (nil_is_neutral_on_append_v0_left V a) at 1.
    rewrite <- (fold_unfold_append_v0_cons V v nil a).
    exact (append_v0_is_associative V (reverse_v1_aux V vs' nil) (v :: nil) a).
Qed.

(* This proof requires light of inductil *)

Lemma reverse_v0_and_reverse_v1_are_equivalent :
  forall (V : Type)
         (vs : list V),
    reverse_v0 V vs = reverse_v1 V vs.
Proof.
  intros V vs.
  unfold reverse_v1.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v1_aux_nil).
    exact (fold_unfold_reverse_v0_nil V).
  - rewrite -> (fold_unfold_reverse_v0_cons V v vs').
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' nil).
    rewrite -> IHvs'.
    symmetry.
    exact (about_reverse_v1_aux V vs' (v :: nil)).
Qed.

(* NOTE
A  methodical way of determining this eureka lemma, because in FPP we prove:

   Proposition reverse_v1_aux_is_involutory:
        forall (V: Type)
               (vs : list V),
          reverse_v1_aux V (reverse_v1_aux V vs nil) nil = vs.
      Proof.
        intros V [ | v vs'].
        - admit.
        - rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' nil).
          (* reverse_v1_aux V (reverse_v1_aux V vs' (v :: nil)) nil = v :: vs' *)
          destruct vs' as [ | v' vs''].
          -- admit.
          -- rewrite -> (fold_unfold_reverse_v1_aux_cons V v' vs'' (v :: nil)).
             (* reverse_v1_aux V (reverse_v1_aux V vs'' (v' :: v :: nil)) nil =
        v :: v' :: vs'' *)
             destruct vs'' as [ | v'' vs'''].
             --- admit.
             --- rewrite -> (fold_unfold_reverse_v1_aux_cons V v'' vs''' (v' :: v :: nil)).
                 (* reverse_v1_aux V (reverse_v1_aux V vs''' (v'' :: v' :: v :: nil)) nil =
        v :: v' :: v'' :: vs''' *)

Therefore, the eureka lemma is:

reverse_v1_aux V (reverse_v1_aux V vs a) nil =
append_v0 V (reverse_v1_aux V a nil) vs
 *)

(* involution *)

(* (1) direct, stand-alone proofs with Eureka lemmas *)

Lemma about_reverse_v1_aux_and_involution_direct:
  forall (V : Type)
         (vs ws : list V),
    reverse_v1_aux V (reverse_v1_aux V vs ws) nil =
    reverse_v1_aux V ws vs.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - intro ws.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V ws).
     reflexivity.
   - intro ws.
     rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' ws).
     Check (IHvs' (v :: ws)).
     rewrite -> (IHvs' (v :: ws)).
     exact (fold_unfold_reverse_v1_aux_cons V v ws vs').
Qed.

Proposition reverse_v1_is_involutory_direct :
  forall (V : Type)
         (vs : list V),
    reverse_v1 V (reverse_v1 V vs) = vs.
Proof.
   intros V vs.
   unfold reverse_v1.
   Check (about_reverse_v1_aux_and_involution_direct V vs nil).
   rewrite -> (about_reverse_v1_aux_and_involution_direct V vs nil).
   exact (fold_unfold_reverse_v1_aux_nil V vs).
Qed.

(* (2) proofs that hinge on the equivalence of reverse_v1 and reverse_v0. *)
Proposition reverse_v1_is_involutory_equivalence :
  forall (V : Type)
         (vs : list V),
    reverse_v1 V (reverse_v1 V vs) = vs.
Proof.
  intros V vs.
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V vs).
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V (reverse_v0 V vs)).
  exact (reverse_v0_is_involutory V vs).
Qed.
        
(* preservation of length *)

(* (1) direct, stand-alone proofs with Eureka lemmas *)
Lemma about_reverse_v1_aux_and_length_direct :
  forall (V : Type)
         (vs ws : list V)
         (n1 n2 : nat),
    length_v0 V vs = n1 ->
    length_v0 V ws = n2 ->
    length_v0 V (reverse_v1_aux V vs ws) = n1 + n2.
Proof.
  intro V.
  induction vs as [ | v vs' IHvs'].
  - intros ws n1 n2 H_length_vs H_length_ws.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V ws).
    rewrite -> (fold_unfold_length_v0_nil V) in H_length_vs.
    rewrite <- H_length_vs.
    rewrite -> (Nat.add_0_l n2).
    exact (H_length_ws).
  - intros ws [ | n1'] n2 H_length_vs H_length_ws.
    -- discriminate.
    -- rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' ws).
       Search (_ = _ -> S _ = S _) .
       apply (eq_S (length_v0 V ws) n2) in H_length_ws.
       rewrite <- (fold_unfold_length_v0_cons V v ws) in H_length_ws.
       rewrite -> (fold_unfold_length_v0_cons V v vs') in H_length_vs.
       injection H_length_vs as H_length_vs.
       rewrite -> (IHvs' (v :: ws) n1' (S n2) H_length_vs H_length_ws).
       symmetry.
       exact (Nat.add_succ_comm n1' n2).
Qed.

(* this proof requires light of inductil *)

Proposition reverse_v1_preserves_length_direct :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (reverse_v1 V vs) = n.
Proof.
  unfold reverse_v1.
  intros V vs n H_length.
  rewrite <- (Nat.add_0_r n).
  exact (about_reverse_v1_aux_and_length_direct V vs nil n 0 H_length (fold_unfold_length_v0_nil V)).
Qed.

Lemma about_reverse_v1_aux_and_length_alt_direct :
  forall (V : Type)
         (vs a: list V),
    length_v0 V (reverse_v1_aux V vs a) = length_v0 V vs + length_v0 V a.
Proof.
  intros V vs.
  induction vs as [ | v vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V a).
    rewrite -> (fold_unfold_length_v0_nil V).
    rewrite -> (Nat.add_0_l (length_v0 V a)).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' a).
    rewrite -> (IHvs' (v :: a)).
    rewrite -> (fold_unfold_length_v0_cons V v a).
    rewrite -> (fold_unfold_length_v0_cons V v vs').
    symmetry.
    exact (Nat.add_succ_comm (length_v0 V vs') (length_v0 V a)).
Qed.

(* this proof requires light of inductil *)

Proposition reverse_v1_preserves_length_alt_direct :
  forall (V : Type)
         (vs : list V),
    length_v0 V (reverse_v1 V vs) = length_v0 V vs.
Proof.
  intros V vs.
  unfold reverse_v1.
  rewrite -> (about_reverse_v1_aux_and_length_alt_direct V vs nil).
  rewrite -> (fold_unfold_length_v0_nil V).
  exact (Nat.add_0_r (length_v0 V vs)).
Qed.

(* (2) proofs that hinge on the equivalence of reverse_v1 and reverse_v0. *)
Proposition reverse_v1_preserves_length_equivalence :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (reverse_v1 V vs) = n.
Proof.
  intros V vs n H_length_vs.
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V vs).
  Check (reverse_v0_preserves_length V vs n H_length_vs).
  exact (reverse_v0_preserves_length V vs n H_length_vs).
Qed.

Proposition reverse_v1_preserves_length_alt_equivalence :
  forall (V : Type)
         (vs : list V),
    length_v0 V (reverse_v1 V vs) = length_v0 V vs.
Proof.
  intros V vs.
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V vs).
  Check (reverse_v0_preserves_length_alt V vs).
  exact (reverse_v0_preserves_length_alt V vs).
Qed.

(* reverse_v1_preserves_length as a corollary of reverse_v1_preserves_length_alt *)

Corollary reverse_v1_preserves_length' :
  forall (V : Type)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 V (reverse_v1 V vs) = n.
Proof.
  intros V vs n H_length.
  rewrite -> (reverse_v1_preserves_length_alt_direct V vs).
  exact (H_length).
Qed.

(* reverse_v1_preserves_length_alt as a corollary of reverse_v0_preserves_length *)

Corollary reverse_v1_preserves_length_alt' :
  forall (V : Type)
         (vs : list V),
    length_v0 V (reverse_v1 V vs) = length_v0 V vs.
Proof.
  intros V vs.
  apply (reverse_v1_preserves_length_direct V vs (length_v0 V vs)).
  reflexivity.
Qed.

(* commutation of append and reverse *)

(* (1) direct, stand-alone proofs with Eureka lemmas *)
Lemma about_commutation_of_append_and_reverse_v1_aux_direct :
  forall (V : Type)
         (v1s v2s a : list V),
    reverse_v1_aux V (append_v0 V v1s v2s) a  = append_v0 V (reverse_v1_aux V v2s nil) (reverse_v1_aux V v1s a).
Proof.
  intro V.
  induction v1s as [ | v1 v1s' IHv1s'].
  - intros v2s a.
    rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_reverse_v1_aux_nil V).
    exact (about_reverse_v1_aux V v2s a).
  - intros v2s a.
    rewrite -> (fold_unfold_append_v0_cons V v1 v1s' v2s).
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v1 (append_v0 V v1s' v2s) a).
    rewrite -> (IHv1s' v2s (v1 :: a)).
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v1 v1s' a).
    reflexivity.
Qed.

(* this proof requires light of inductil *)

Proposition append_and_reverse_v1_commute_with_each_other_direct :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v1 V (append_v0 V v1s v2s) = append_v0 V (reverse_v1 V v2s) (reverse_v1 V v1s).
Proof.
  intros V v1s v2s.
  unfold reverse_v1.
  exact (about_commutation_of_append_and_reverse_v1_aux_direct V v1s v2s nil).
Qed.

(* (2) proofs that hinge on the equivalence of reverse_v1 and reverse_v0. *)
Proposition append_and_reverse_v1_commute_with_each_other_equivalence :
  forall (V : Type)
         (v1s v2s : list V),
    reverse_v1 V (append_v0 V v1s v2s) = append_v0 V (reverse_v1 V v2s) (reverse_v1 V v1s).
Proof.
  intros V v1s v2s.
  Check (reverse_v0_and_reverse_v1_are_equivalent V (append_v0 V v1s v2s)).
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V (append_v0 V v1s v2s)).
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V v1s).
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V v2s).
  Check (append_and_reverse_v0_commute_with_each_other V v1s v2s).
  exact (append_and_reverse_v0_commute_with_each_other V v1s v2s).
Qed.

(* ********** *)

(* A study of the polymorphic map function: *)

Definition specification_of_map (map : forall V W : Type, (V -> W) -> list V -> list W) :=
  (forall (V W : Type)
          (f : V -> W),
      map V W f nil = nil)
  /\
  (forall (V W : Type)
          (f : V -> W)
          (v : V)
          (vs' : list V),
      map V W f (v :: vs') = f v :: map V W f vs').

(* Task 7:

   a. Prove whether the specification specifies at most one map function.
*)

Proposition there_is_at_most_one_map_function :
  forall map1 map2 : forall V W : Type, (V -> W) -> list V -> list W,
      specification_of_map map1 ->
      specification_of_map map2 ->
      forall (V W : Type)
             (f : V -> W)
             (vs : list V),
        map1 V W f vs = map2 V W f vs.
Proof.
  intros map1 map2 S_map1 S_map2 V W f vs.
  induction vs as [ | v vs' IHvs'].
  - unfold specification_of_map in S_map1.
    destruct S_map1 as [fold_unfold_map1_nil _].
    destruct S_map2 as [fold_unfold_map2_nil _].
    rewrite -> (fold_unfold_map2_nil V W f).
    exact (fold_unfold_map1_nil V W f).
  - unfold specification_of_map in S_map1.
    destruct S_map1 as [_ fold_unfold_map1_cons].
    destruct S_map2 as [_ fold_unfold_map2_cons].
    rewrite -> (fold_unfold_map1_cons V W f v vs').
    rewrite -> (fold_unfold_map2_cons V W f v vs').
    rewrite -> IHvs'.
    reflexivity.
Qed.

(*
   b. Implement the map function in direct style.
*)

Fixpoint map_v0 (V W : Type) (f : V -> W) (vs : list V) : list W :=
  match vs with
  | nil =>
    nil
  | v :: vs' =>
    f v :: map_v0 V W f vs'
  end.

(*
   c. State the associated fold-unfold lemmas.
*)

Lemma fold_unfold_map_v0_nil :
  forall (V W : Type)
         (f : V -> W),
    map_v0 V W f nil =
    nil.
Proof.
  fold_unfold_tactic map_v0.
Qed.

Lemma fold_unfold_map_v0_cons :
  forall (V W : Type)
         (f : V -> W)
         (v : V)
         (vs' : list V),
    map_v0 V W f (v :: vs') =
    f v :: map_v0 V W f vs'.
Proof.
  fold_unfold_tactic map_v0.
Qed.

(*
   d. Prove whether your implementation satisfies the specification.
*)

Proposition map_v0_satisfies_the_specification_of_map :
  specification_of_map map_v0.
Proof.
  unfold specification_of_map.
  split.
  - exact fold_unfold_map_v0_nil.
  - exact fold_unfold_map_v0_cons.
Qed.

(*
   e. Implement the copy function using map_v0.
*)

Definition copy_v2 (V : Type) (vs : list V) : list V :=
  map_v0 V V (fun x : V  =>  x) vs.

Compute test_copy copy_v2.
(* 
     = true
     : bool
*)


(*
Hint: Does copy_v2 satisfy the specification of copy?
*)

Theorem copy_2_satisfies_the_specification_of_copy :
  specification_of_copy copy_v2.
Proof.
  unfold specification_of_copy, copy_v2.
  split.
  - intro V.
    exact (fold_unfold_map_v0_nil V V (fun x : V => x)).
  - intros V v vs'.
    exact (fold_unfold_map_v0_cons V V (fun x : V => x) v vs').
Qed.

(*
   f. Prove whether mapping a function over a list preserves the length of this list.
 *)

Proposition map_preserves_length :
  forall (V W : Type)
         (f : V -> W)
         (vs : list V)
         (n : nat),
    length_v0 V vs = n ->
    length_v0 W (map_v0 V W f vs) = n.
Proof.
  intros V W f.
  induction vs as [ | v vs' IHvs'].
  - intros n H_length.
    rewrite -> (fold_unfold_map_v0_nil V W f).
    exact H_length.
  - intros [ | n'] H_length.
    -- discriminate H_length.
    -- rewrite -> (fold_unfold_map_v0_cons V W f v vs').
       rewrite -> (fold_unfold_length_v0_cons W (f v) (map_v0 V W f vs')).
       Check (IHvs' n'). (*  length_v0 V vs' = n' -> length_v0 W (map_v0 V W f vs') = n' *)
       rewrite -> (fold_unfold_length_v0_cons V v vs') in H_length.
       injection H_length as H_length.
       rewrite -> (IHvs' n' H_length).
       reflexivity.
Qed.

(* this proof requires light of inductil *)

Proposition map_preserves_length_alt :
  forall (V W : Type)
         (f : V -> W)
         (vs : list V),
    length_v0 W (map_v0 V W f vs) = length_v0 V vs.
Proof.
  intros V W f.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_map_v0_nil V W f).
    reflexivity.
  - rewrite -> (fold_unfold_map_v0_cons V W f v vs').
    rewrite -> (fold_unfold_length_v0_cons W (f v) (map_v0 V W f vs')).
    rewrite -> (IHvs').
    rewrite -> (fold_unfold_length_v0_cons V v vs').
    reflexivity.
Qed.

(* this proof does not require light of inductil *)

(*
   g. Do map_v0 and append_v0 commute with each other and if so how?
 *)

Proposition append_v0_and_map_v0_commute_with_each_other :
  forall (V W : Type)
         (f : V -> W)
         (v1s v2s: list V),
    map_v0 V W f (append_v0 V v1s v2s) = append_v0 W (map_v0 V W f v1s) (map_v0 V W f v2s).
Proof.
  intros V W f v1s v2s.
  induction v1s as [ | v1' v1s' IHv1s'].
  - rewrite -> (fold_unfold_append_v0_nil V v2s).
    rewrite -> (fold_unfold_map_v0_nil V W f).
    rewrite -> (fold_unfold_append_v0_nil W (map_v0 V W f v2s)).
    reflexivity.
  - rewrite -> (fold_unfold_map_v0_cons V W f v1' v1s').
    rewrite -> (fold_unfold_append_v0_cons W (f v1') (map_v0 V W f v1s') (map_v0 V W f v2s)).
    rewrite <- (IHv1s').
    rewrite -> (fold_unfold_append_v0_cons V v1' v1s' v2s).
    exact (fold_unfold_map_v0_cons V W f v1' (append_v0 V v1s' v2s)).
Qed.

(* this proof does not require light of inductil *)

(*
   h. Do map_v0 and reverse_v0 commute with each other and if so how?
*)

Proposition map_v0_reverse_v0_commute_with_each_other :
  forall (V W : Type)
         (f : V -> W)
         (vs: list V),
    map_v0 V W f (reverse_v0 V vs) = reverse_v0 W (map_v0 V W f vs).
Proof.
  intros V W f.
  induction vs as [ | v vs' IHvs'].
  - rewrite -> (fold_unfold_reverse_v0_nil V).
    rewrite -> (fold_unfold_map_v0_nil V W f).
    rewrite -> (fold_unfold_reverse_v0_nil W).
    reflexivity.
  - rewrite -> (fold_unfold_map_v0_cons V W f v vs').
    rewrite -> (fold_unfold_reverse_v0_cons W (f v) (map_v0 V W f vs')).
    rewrite <- IHvs' .
    rewrite -> (fold_unfold_reverse_v0_cons V v vs').
    rewrite <- (fold_unfold_map_v0_nil V W f).
    rewrite <- (fold_unfold_map_v0_cons V W f v nil).
    rewrite -> (append_v0_and_map_v0_commute_with_each_other V W f (reverse_v0 V vs') (v :: nil)).
    reflexivity.
Qed.

(*
   i. Do map_v0 and reverse_v1 commute with each other and if so how?
      This subtask is optional.
*)

(* (1) direct, stand-alone proofs with Eureka lemmas *)
(* we first write a more general Proposition about reverse_v1 so that the accumulator is also mapped *)
Proposition map_v0_reverse_v1_aux_commute_with_each_other_direct :
  forall (V W : Type)
         (f : V -> W)
         (vs a : list V),
    map_v0 V W f (reverse_v1_aux V vs a) = reverse_v1_aux W (map_v0 V W f vs) (map_v0 V W f a).
Proof.
  intros V W f vs.
  induction vs as [ | v vs' IHvs'].
  - intro a.
    rewrite -> (fold_unfold_reverse_v1_aux_nil V a).
    rewrite -> (fold_unfold_map_v0_nil V W f).
    rewrite -> (fold_unfold_reverse_v1_aux_nil W (map_v0 V W f a)).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_reverse_v1_aux_cons V v vs' a).
    rewrite -> (fold_unfold_map_v0_cons V W f v vs').
    rewrite -> (IHvs' (v :: a)).
    rewrite -> (fold_unfold_reverse_v1_aux_cons W (f v) (map_v0 V W f vs') (map_v0 V W f a)).
    rewrite -> (fold_unfold_map_v0_cons V W f v a).
    reflexivity.
Qed.

(* this proof requires light of inductil *)

Proposition map_v0_reverse_v1_commute_with_each_other_direct :
  forall (V W : Type)
         (f : V -> W)
         (vs : list V),
    map_v0 V W f (reverse_v1 V vs) = reverse_v1 W (map_v0 V W f vs).
Proof.
  intros V W f vs.
  unfold reverse_v1.
  Check (map_v0_reverse_v1_aux_commute_with_each_other_direct V W f vs nil).
  rewrite -> (map_v0_reverse_v1_aux_commute_with_each_other_direct V W f vs nil).
  rewrite -> (fold_unfold_map_v0_nil V W f).
  reflexivity.
Qed.

(* (2) proofs that hinge on the equivalence of reverse_v1 and reverse_v0. *)
Proposition map_v0_reverse_v1_commute_with_each_other_equivalence :
  forall (V W : Type)
         (f : V -> W)
         (vs : list V),
    map_v0 V W f (reverse_v1 V vs) = reverse_v1 W (map_v0 V W f vs).
Proof.
  intros V W f vs.
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent V vs).
  rewrite <- (reverse_v0_and_reverse_v1_are_equivalent W (map_v0 V W f vs)).
  exact (map_v0_reverse_v0_commute_with_each_other V W f vs).
Qed.

(*
   j. Define a unit-test function for the map function
      and verify that your implementation satisfies it.
 *)


Definition test_map (candidate : forall V W : Type, (V -> W) -> list V -> list W) : bool :=
  (eqb_list nat beq_nat (candidate nat nat (fun n => n + 1) (2 :: 1 :: nil)) (3 :: 2 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat nat (fun n => n + n) (2 :: 1 :: nil)) (4 :: 2 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat nat (fun n => n - 1) (4 :: 3 :: 2 :: 1 :: nil)) (3 :: 2 :: 1 :: 0 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat nat (fun n => n - 2) (4 :: 3 :: 2 :: nil)) (2 :: 1 :: 0 :: nil) ) &&
  (eqb_list nat beq_nat (candidate nat nat (fun n => n + n + n) (2 ::  nil)) (6 ::  nil)) &&
  (eqb_list nat beq_nat (candidate nat nat (fun n => n) (2 ::  nil)) (2 ::  nil)) &&
  (eqb_list nat Nat.eqb (candidate nat nat (fun x : nat => x) nil) nil) &&
  (eqb_list nat Nat.eqb (candidate nat nat (fun x : nat => x) (2 :: 1 :: 0 :: nil)) (2 :: 1 :: 0 :: nil)) &&
  (eqb_list nat Nat.eqb (candidate nat nat (fun x : nat => 2 * x) (2 :: 1 :: 0 :: nil)) (4 :: 2 :: 0 :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool bool (fun x : bool => x) nil) nil) &&
  (eqb_list bool Bool.eqb (candidate bool bool (fun x : bool => x) (true :: false :: nil)) (true :: false :: nil)) &&
  (eqb_list bool Bool.eqb (candidate bool bool (fun x : bool =>
                                                  match x with
                                                  | true => false
                                                  | false => true
                                                  end) (true :: false :: nil)) (false :: true :: nil)).


Compute test_map map_v0.
(* 
     = true
     : bool
*)

(* ********** *)

(* A study of the polymorphic fold-right and fold-left functions: *)

Definition specification_of_list_fold_right (list_fold_right : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     list_fold_right V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     list_fold_right V W nil_case cons_case (v :: vs') =
     cons_case v (list_fold_right V W nil_case cons_case vs')).

Definition specification_of_list_fold_left (list_fold_left : forall V W : Type, W -> (V -> W -> W) -> list V -> W) :=
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W),
     list_fold_left V W nil_case cons_case nil =
     nil_case)
  /\
  (forall (V W : Type)
          (nil_case : W)
          (cons_case : V -> W -> W)
          (v : V)
          (vs' : list V),
     list_fold_left V W nil_case cons_case (v :: vs') =
     list_fold_left V W (cons_case v nil_case) cons_case vs').

(* Task 8:

   a. Implement the fold-right function in direct style.
*)

Fixpoint list_fold_right (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    cons_case v (list_fold_right V W nil_case cons_case vs')
  end.

(*
   b. Implement the fold-left function in direct style.
*)

Fixpoint list_fold_left (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  match vs with
  | nil =>
    nil_case
  | v :: vs' =>
    list_fold_left V W (cons_case v nil_case) cons_case vs'
  end.

(*
   c. state the fold-unfold lemmas associated to list_fold_right and to list_fold_left
*)

Lemma fold_unfold_list_fold_right_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_right V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_right_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_right V W nil_case cons_case (v :: vs') =
    cons_case v (list_fold_right V W nil_case cons_case vs').
Proof.
  fold_unfold_tactic list_fold_right.
Qed.

Lemma fold_unfold_list_fold_left_nil :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W),
    list_fold_left V W nil_case cons_case nil =
    nil_case.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

Lemma fold_unfold_list_fold_left_cons :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    list_fold_left V W nil_case cons_case (v :: vs') =
    list_fold_left V W (cons_case v nil_case) cons_case vs'.
Proof.
  fold_unfold_tactic list_fold_left.
Qed.

(*
   d. Prove that each of your implementations satisfies the corresponding specification.
*)

Theorem list_fold_right_satisfies_specification_of_list_fold_right :
  specification_of_list_fold_right list_fold_right.

Proof.
  unfold specification_of_list_fold_right.
  split.
  - exact (fold_unfold_list_fold_right_nil).
  - exact (fold_unfold_list_fold_right_cons).
Qed.

Theorem list_fold_left_satisfies_specification_of_list_fold_left :
  specification_of_list_fold_left list_fold_left.

Proof.
  unfold specification_of_list_fold_left.
  split.
  - exact (fold_unfold_list_fold_left_nil).
  - exact (fold_unfold_list_fold_left_cons).
Qed.

(*
   e. Which function do foo and bar (defined just below) compute?
*)


Definition foo (V : Type) (vs : list V) :=
  list_fold_right V (list V) nil (fun v vs => v :: vs) vs.

Compute foo nat (1 :: 2 :: 3 :: nil).
(*
     = 1 :: 2 :: 3 :: nil
     : list nat
 *)

Proposition foo_satisfies_specification_of_copy :
  specification_of_copy foo.
Proof.
  unfold specification_of_copy, foo.
  split.
  - intro V.
    Check (fold_unfold_list_fold_right_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
    exact (fold_unfold_list_fold_right_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v vs'.
    Check (fold_unfold_list_fold_right_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
    exact (fold_unfold_list_fold_right_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
Qed.

(* foo is the identity/copy function for lists *)

Definition bar (V : Type) (vs : list V) :=
  list_fold_left V (list V) nil (fun v vs => v :: vs) vs.

Compute bar nat (1 :: 2 :: 3 :: nil).
(*
     = 3 :: 2 :: 1 :: nil
     : list nat
 *)

(*
Lemma bar_satisfies_specification_of_reverse_aux :
  forall append: forall V : Type, list V -> list V -> list V,
    specification_of_append append ->
    forall (V : Type)
           (cons_case : V -> list V -> list V)
           (vs : list V),
      append V (list_fold_left V (list V) nil cons_case vs') vs = list_fold_left V (list V) vs cons_case vs'.
      
 *)

 (*Lemma about_bar : *)
  


Proposition bar_satisfies_specification_of_reverse :
  specification_of_reverse bar.
Proof.
  unfold specification_of_reverse, bar.
  intros append spec_append.
  split.
  - intros V.
    Check (fold_unfold_list_fold_left_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
    exact (fold_unfold_list_fold_left_nil V (list V) nil (fun (v : V) (vs : list V) => v :: vs)).
  - intros V v vs'.
    Check (fold_unfold_list_fold_left_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
    rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v vs').
    destruct spec_append as [a_0 a_1].
    revert v.
    Check fold_unfold_list_fold_left_cons  V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs).
    induction vs' as [ | v' vs'' IHvs'].
    -- intro v.
       rewrite -> (fold_unfold_list_fold_left_nil V (list V) (v :: nil)              (fun (v0 : V) (vs : list V) => v0 :: vs)).
       rewrite -> (fold_unfold_list_fold_left_nil V (list V) (nil)              (fun (v0 : V) (vs : list V) => v0 :: vs)).
       rewrite -> (a_0 V (v :: nil)).
       reflexivity.
    -- rewrite -> (fold_unfold_list_fold_left_cons V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs) v' vs'').    
Admitted.

(*
  append : forall W : Type, list W -> list W -> list W
  H : forall (V : Type) (v2s : list V), append V nil v2s = v2s
  H0 : forall (V : Type) (v1 : V) (v1s' v2s : list V),
       append V (v1 :: v1s') v2s = v1 :: append V v1s' v2s
  V : Type
  v : V
  vs' : list V
  ============================
  list_fold_left V (list V) (v :: nil)
    (fun (v0 : V) (vs : list V) => v0 :: vs) vs' =
  append V
    (list_fold_left V (list V) nil (fun (v0 : V) (vs : list V) => v0 :: vs)
       vs') (v :: nil)
*)


(* bar reverse function for lists *)


(*
   f. Implement the length function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition length_v2 (V : Type) (vs : list V) : nat :=
  list_fold_right V nat 0 (fun _ ih => S (ih)) vs.

Compute test_length length_v2.

Definition length_v3 (V : Type) (vs : list V) : nat :=
  list_fold_left V nat 0 (fun _ a => S a) vs.

Compute test_length length_v3.

(* both fold left and fold right work because reversing a list does not change its length,
   as proved earlier *)

(*
   g. Implement the copy function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition copy_v3 (V : Type) (vs : list V) : list V :=
  list_fold_right V (list V) nil (fun v ih => v :: ih) vs.

Compute test_copy copy_v3.

(* list_fold_right is the better choice here,
   because implementing copy using list_fold_left would be accomplished either by
   applying list_fold_left to the given list using the same nil and cons case as in copy_v3,
   and then reversing the result,
   or, alternatively,
   reversing the given list
   and then applying list_fold_left to the result using the same nil and cons case as in copy_v3,
   both of which are less efficient than simply using list_fold_right *)

(*
   h. Implement the append function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition append_v1 (V : Type) (v1s v2s : list V) : list V :=
  list_fold_right V (list V) v2s (fun v ih => v :: ih) v1s.

Compute test_append append_v1.

(* list_fold_right is a better choice,
   because implementing append using list_fold_left would be accomplished either by
   applying list_fold_left to the given list and then reversing the result,
   or, alternatively,
   reversing the given list
   and then applying list_fold_left to the result, 
   both of which are less efficient than simply using list_fold_right *)

(*
   i. Implement the reverse function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition reverse_v2 (V : Type) (vs : list V) : list V :=
  list_fold_left V (list V) nil (fun v a => v :: a) vs.

Compute test_reverse reverse_v2.

(* list_fold_left is a better choice. *)
   

(*
   j. Implement the map function using either list_fold_right or list_fold_left, and justify your choice.
*)

Definition map_v2 (V W : Type) (f : V -> W) (vs : list V) : list W :=
  list_fold_right V (list W) nil (fun v ih  => (f v) :: ih) vs.

Compute test_map map_v2.

(* list_fold_right is a better choice because we are returning a list of the same order as the initial list.
   Using list_fold_left would require us to reverse the resulting list to get the mapped list. *)

(*
   k. Relate list_fold_right and list_fold_left using the reverse function.
*)

Definition list_fold_right_v1 (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_left V W nil_case cons_case (reverse_v0 V vs).

Definition list_fold_left_v1 (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_right V W nil_case cons_case (reverse_v0 V vs).

(*
   l. Implement list_fold_right using list_fold_left, without using the reverse function.
*)

Definition list_fold_right_v2 (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
  list_fold_left V
                 (W -> W)
                 (fun a => a)
                 (fun v ih => fun a => ih (cons_case v a))
                 vs
                 nil_case.

(*
   m. Implement list_fold_left using list_fold_right, without using the reverse function.
*)

Definition list_fold_left_v2 (V W : Type) (nil_case : W) (cons_case : V -> W -> W) (vs : list V) : W :=
    list_fold_right V
                    (W -> W)
                    (fun a => a)
                    (fun v ih => fun a => ih (cons_case v a))
                    vs
                    nil_case.

(* Testing list_fold_right/left_v1/v2 *)

Definition length_v4 (V : Type) (l : list V) :=
  list_fold_right_v1 V nat 0 (fun _ a => S a) l.

Definition length_v5 (V : Type) (l : list V) :=
  list_fold_right_v2 V nat 0 (fun _ a => S a) l.

Compute test_length length_v4 && test_length length_v5.

Definition length_v6 (V : Type) (l : list V) :=
  list_fold_left_v1 V nat 0 (fun _ a => S a) l.

Definition length_v7 (V : Type) (l : list V) :=
  list_fold_left_v2 V nat 0 (fun _ a => S a) l.

Compute test_length length_v6 && test_length length_v7.


Definition append_v4 (V : Type) (l1 l2 : list V) :=
  list_fold_right_v1 V (list V) l2 (fun v ih => v :: ih) l1.

Definition append_v5 (V : Type) (l1 l2 : list V) :=
  list_fold_right_v2 V (list V) l2 (fun v ih => v :: ih) l1.

Compute test_append append_v4 && test_append append_v5.

Definition append_v6 (V : Type) (l1 l2 : list V) :=
  list_fold_left_v1 V (list V) (l2) (fun v ih => v :: ih) (reverse_v1 V l1).

Definition append_v7 (V : Type) (l1 l2 : list V) :=
  list_fold_left_v2 V (list V) (l2) (fun v ih => v :: ih) (reverse_v1 V l1).

Compute test_append append_v6 && test_append append_v7.


Definition copy_v4 (V : Type) (l : list V) :=
  list_fold_right_v1 V (list V) nil (fun v ih => v :: ih) l.

Definition copy_v5 (V : Type) (l : list V) :=
  list_fold_right_v2 V (list V) nil (fun v ih => v :: ih) l.

Compute test_copy copy_v4 && test_copy copy_v5.

Definition copy_v6 (V : Type) (l : list V) :=
  list_fold_left_v1 V (list V) nil (fun v ih => v :: ih) (reverse_v1 V l).

Definition copy_v7 (V : Type) (l : list V) :=
  list_fold_left_v2 V (list V) nil (fun v ih => v :: ih) (reverse_v1 V l).

Compute test_copy copy_v6 && test_copy copy_v7.

Definition copy_v8 (V : Type) (l : list V) := append_v4 V l nil.

Definition copy_v9 (V : Type) (l : list V) := append_v6 V l nil.

Compute test_copy copy_v8 && test_copy copy_v9.


Definition reverse_v4 (V : Type) (l : list V) :=
  list_fold_right_v1 V (list V) nil (fun v ih => v :: ih) (reverse_v1 V l).

Definition reverse_v5 (V : Type) (l : list V) :=
  list_fold_right_v2 V (list V) nil (fun v ih => v :: ih) (reverse_v1 V l).

Compute test_reverse reverse_v4 && test_reverse reverse_v5.

Definition reverse_v6 (V : Type) (l : list V) :=
  list_fold_left_v1 V (list V) nil (fun v ih => v :: ih) l.

Definition reverse_v7 (V : Type) (l : list V) :=
  list_fold_left_v2 V (list V) nil (fun v ih => v :: ih) l.

Compute test_reverse reverse_v6 && test_reverse reverse_v7.

                                                

(*
   n. Show that
      if the cons case is a function that is left permutative,
      applying list_fold_left and applying list_fold_right
      to a nil case, this cons case, and a list
      give the same result
*)
  
Definition is_left_permutative (V W : Type) (op2 : V -> W -> W) :=
  forall (v1 v2 : V)
         (v3 : W),
    op2 v1 (op2 v2 v3) = op2 v2 (op2 v1 v3).

Lemma about_list_fold_left :
  forall (V W : Type)
         (nil_case : W)
         (cons_case : V -> W -> W)
         (v : V)
         (vs' : list V),
    is_left_permutative V W cons_case ->
    list_fold_left V W (cons_case v nil_case) cons_case vs' =
    cons_case v (list_fold_left V W nil_case cons_case vs').

Proof.
  intros V W nil_case cons_case v vs' H_cons_is_left_permutative.
  revert nil_case.
  induction vs' as [ | v' vs'' IHvs''].
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_left_nil V W (cons_case v nil_case) cons_case).
    rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    reflexivity.
  - intro nil_case.
    rewrite -> (fold_unfold_list_fold_left_cons V W (cons_case v nil_case) cons_case v' vs'').
    rewrite -> (H_cons_is_left_permutative v' v nil_case).
    rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v' vs'').
    rewrite -> (IHvs'' (cons_case v' nil_case)).
    reflexivity.
Qed.

Theorem the_grand_finale :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    is_left_permutative V W cons_case ->
    forall (nil_case : W)
           (vs : list V),
      list_fold_left  V W nil_case cons_case vs =
      list_fold_right V W nil_case cons_case vs.
Proof.
  intros V W cons_case H_cons_case_is_left_permutative nil_case.
  induction vs as [ | v' vs' IHvs'].
  - rewrite -> (fold_unfold_list_fold_left_nil V W nil_case cons_case).
    exact (fold_unfold_list_fold_right_nil V W nil_case cons_case).
  - rewrite -> (fold_unfold_list_fold_left_cons V W nil_case cons_case v' vs'). 
    rewrite -> (fold_unfold_list_fold_right_cons V W nil_case cons_case v' vs').
    rewrite -> (about_list_fold_left V W nil_case cons_case v' vs' H_cons_case_is_left_permutative).
    rewrite -> (IHvs').
    reflexivity.
Qed.

(*
   o. Can you think of corollaries of this property?
*)


Lemma length_cons_case_is_left_permutative :
  forall (V : Type),
    is_left_permutative (V : Type) nat (fun (_ : V) (a : nat) => S a).
Proof.
  intro V.
  unfold is_left_permutative.
  intros e1 e2 n.
  reflexivity.
Qed.

Corollary length_is_equivalent_if_constructed_with_fold_left_or_fold_right :
  forall (V : Type) (vs : list V),
    length_v3 V vs = length_v2 V vs.
Proof.
  intro V.
  unfold length_v2, length_v3.
  Check (the_grand_finale V nat (fun (_ : V) (ih : nat) => S ih)
                          (length_cons_case_is_left_permutative V) 0).
  apply (the_grand_finale V nat (fun (_ : V) (ih : nat) => S ih)
                          (length_cons_case_is_left_permutative V) 0).
Qed.

(*
   o. Can you think of corollaries of this property?
*)

Lemma plus_is_left_permutative :
  is_left_permutative nat nat plus.
Proof.
  unfold is_left_permutative.
  intros v1 v2 v3.
  rewrite -> (Nat.add_assoc v1 v2 v3).
  rewrite -> (Nat.add_comm v1 v2).
  rewrite <- (Nat.add_assoc v2 v1 v3).
  reflexivity.
Qed.

Corollary example_for_plus :
  forall ns : list nat,
    list_fold_left nat nat 0 plus ns = list_fold_right nat nat 0 plus ns.
Proof.
  Check (the_grand_finale nat nat plus plus_is_left_permutative 0).
  exact (the_grand_finale nat nat plus plus_is_left_permutative 0).
Qed.

(* What do you make of this corollary?
The corollary makes sense because the sum of the elements of a list is unaffected by their order in the list
so reversing a list will not change the sum of its elements.
*)

(*
   Can you think of more such corollaries?
*)

Lemma mult_is_left_permutative :
  is_left_permutative nat nat Nat.mul.
Proof.
  unfold is_left_permutative.
  intros v1 v2 v3.
  rewrite -> (Nat.mul_assoc v1 v2 v3).
  rewrite -> (Nat.mul_comm v1 v2).
  rewrite <- (Nat.mul_assoc v2 v1 v3).
  reflexivity.
Qed.

Corollary folding_mult :
  forall ns : list nat,
    list_fold_left nat nat 1 Nat.mul ns = list_fold_right nat nat 1 Nat.mul ns.
Proof.
  Check (the_grand_finale nat nat Nat.mul mult_is_left_permutative 1).
  exact (the_grand_finale nat nat Nat.mul mult_is_left_permutative 1).
Qed.

(* length is also a corollary *)

(*
   p. Subsidiary question: does the converse of Theorem the_grand_finale hold?
*)

Theorem the_grand_finale_converse :
  forall (V W : Type)
         (cons_case : V -> W -> W),
    (forall (nil_case : W)
            (vs : list V),
        list_fold_left  V W nil_case cons_case vs =
        list_fold_right V W nil_case cons_case vs) ->
    is_left_permutative V W cons_case.
Proof.
  intros V W cons_case H_equality_of_folding.
  unfold is_left_permutative.
  intros v1 v2 w3.
  Check (H_equality_of_folding w3 (v1 :: v2 :: nil)).
  assert (ly := H_equality_of_folding w3 (v1 :: v2 :: nil)).
  rewrite -> (fold_unfold_list_fold_left_cons V W w3 cons_case v1 (v2 :: nil)) in ly.
  rewrite -> (fold_unfold_list_fold_left_cons V W (cons_case v1 w3) cons_case v2 nil) in ly.
  rewrite -> (fold_unfold_list_fold_left_nil V W (cons_case v2 (cons_case v1 w3)) cons_case) in ly.
  rewrite -> (fold_unfold_list_fold_right_cons V W w3 cons_case v1 (v2 :: nil)) in ly.
  rewrite -> (fold_unfold_list_fold_right_cons V W w3 cons_case v2 nil) in ly.
  rewrite -> (fold_unfold_list_fold_right_nil V W w3 cons_case) in ly.
  symmetry.
  exact ly.
Qed.

(* ********** *)

(* Task 9: *)

Fixpoint nat_fold_right (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s (nat_fold_right V z s n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_right V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_right V z s (S n') =
    s (nat_fold_right V z s n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

(* ***** *)

Fixpoint nat_fold_left (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_fold_left V (s z) s n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_left V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_left V z s (S n') =
    nat_fold_left V (s z) s n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ********** *)

(* Task 10: *)

Fixpoint nat_parafold_right (V : Type) (zero_case : V) (succ_case : nat -> V -> V) (n : nat) : V :=
  match n with
  | O =>
    zero_case
  | S n' =>
    succ_case n' (nat_parafold_right V zero_case succ_case n')
  end.

Lemma fold_unfold_nat_parafold_right_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : nat -> V -> V),
    nat_parafold_right V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_parafold_right.
Qed.

Lemma fold_unfold_nat_parafold_right_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : nat -> V -> V)
         (n' : nat),
    nat_parafold_right V zero_case succ_case (S n') =
    succ_case n' (nat_parafold_right V zero_case succ_case n').
Proof.
  fold_unfold_tactic nat_parafold_right.
Qed.

(* ***** *)

Fixpoint nat_parafold_left (V : Type) (zero_case : V) (succ_case : nat -> V -> V) (n : nat) : V :=
  match n with
  | O =>
    zero_case
  | S n' =>
    nat_parafold_left V (succ_case n' zero_case) succ_case n'
  end.

Lemma fold_unfold_nat_parafold_left_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : nat -> V -> V),
    nat_parafold_left V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_parafold_left.
Qed.

Lemma fold_unfold_nat_parafold_left_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : nat -> V -> V)
         (n' : nat),
    nat_parafold_left V zero_case succ_case (S n') =
    nat_parafold_left V (succ_case n' zero_case) succ_case n'.
Proof.
  fold_unfold_tactic nat_parafold_left.
Qed.

(* ***** *)

Definition specification_of_fac (fac : nat -> nat) :=
  (fac 0 = 1)
  /\
  (forall n' : nat,
    fac (S n') = S n' * fac n').

Definition test_fac (candidate : nat -> nat) : bool :=
  (candidate 0 =n= 1)
  &&
  (candidate 1 =n= 1 * 1)
  &&
  (candidate 2 =n= 2 * 1 * 1)
  &&
  (candidate 3 =n= 3 * 2 * 1 * 1)
  &&
  (candidate 4 =n= 4 * 3 * 2 * 1 * 1)
  &&
  (candidate 5 =n= 5 * 4 * 3 * 2 * 1 * 1).

Fixpoint fac_v0 (n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    S n' * fac_v0 n'
  end.

Compute (test_fac fac_v0).

Lemma fold_unfold_fac_v0_O :
  fac_v0 0 =
  1.
Proof.
  fold_unfold_tactic fac_v0.
Qed.

Lemma fold_unfold_fac_v0_S :
  forall n' : nat,
    fac_v0 (S n') =
    S n' * fac_v0 n'.
Proof.
  fold_unfold_tactic fac_v0.
Qed.

Definition fac_v1 (n : nat) : nat :=
  nat_parafold_right nat 1 (fun i ih => S i * ih) n.

Compute (test_fac fac_v1).

(* ********** *)

(* end of midterm-project.v *)
