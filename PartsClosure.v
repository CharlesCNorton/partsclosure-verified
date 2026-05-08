(******************************************************************************)
(*                                                                            *)
(*          Parts Closure: Verified Bootstrap-Manufacturable Subset           *)
(*                                                                            *)
(*     Closure of a parts list under the make-from relation. The closure      *)
(*     is the largest subset where every part can be manufactured from        *)
(*     some other parts in the subset using verified machines.                *)
(*                                                                            *)
(*     "Every monotone map has a fixed point."                                *)
(*     - Alfred Tarski, 1955                                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: May 8, 2026                                                      *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

(* ========================================================================== *)
(* 1. Parts and recipes.                                                      *)
(* ========================================================================== *)

(* Parts are identified by a type with decidable equality. Natural numbers    *)
(* serve as concrete witnesses; the development is parametric otherwise.      *)

Definition Part := nat.

Definition Part_eq_dec : forall (x y : Part), {x = y} + {x <> y} := Nat.eq_dec.

(* A recipe consumes a list of input parts and produces a single output       *)
(* part. A part with no recipe producing it is, by construction, never in     *)
(* any closed subset (Theorem no_recipe_excluded below).                      *)

Record Recipe : Type := mkRecipe {
  inputs : list Part;
  output : Part
}.

Definition Catalog := list Recipe.

(* ========================================================================== *)
(* 2. Decidable membership and subset.                                        *)
(* ========================================================================== *)

Fixpoint mem (x : Part) (l : list Part) : bool :=
  match l with
  | [] => false
  | y :: rest => if Part_eq_dec x y then true else mem x rest
  end.

Lemma mem_iff_In : forall (x : Part) (l : list Part),
  mem x l = true <-> In x l.
Proof.
  intros x l. induction l as [|y rest IH].
  - cbn. split.
    + intros H. discriminate.
    + intros H. destruct H.
  - cbn. destruct (Part_eq_dec x y) as [E | NE].
    + split.
      * intros _. left. symmetry. exact E.
      * intros _. reflexivity.
    + rewrite IH. split.
      * intros H. right. exact H.
      * intros [H | H]; [symmetry in H; contradiction | exact H].
Qed.

Definition subset_b (s1 s2 : list Part) : bool :=
  forallb (fun x => mem x s2) s1.

Lemma subset_b_iff_incl : forall s1 s2 : list Part,
  subset_b s1 s2 = true <-> incl s1 s2.
Proof.
  intros s1 s2. unfold subset_b, incl.
  rewrite forallb_forall. split; intros H x Hin.
  - apply mem_iff_In. apply H. exact Hin.
  - apply mem_iff_In. apply H. exact Hin.
Qed.

(* ========================================================================== *)
(* 3. Producibility.                                                          *)
(* ========================================================================== *)

(* A recipe r produces p from the supply set S when its output is p and       *)
(* every one of its inputs lies in S.                                         *)

Definition producible_by (r : Recipe) (S : list Part) (p : Part) : bool :=
  match Part_eq_dec (output r) p with
  | left _  => subset_b (inputs r) S
  | right _ => false
  end.

Definition producible (C : Catalog) (S : list Part) (p : Part) : bool :=
  existsb (fun r => producible_by r S p) C.

Lemma producible_correct : forall (C : Catalog) (S : list Part) (p : Part),
  producible C S p = true <->
  (exists r, In r C /\ output r = p /\ incl (inputs r) S).
Proof.
  intros C S p. unfold producible. rewrite existsb_exists. split.
  - intros [r [Hin Hpb]]. exists r. unfold producible_by in Hpb.
    destruct (Part_eq_dec (output r) p) as [Eq | NEq]; [|discriminate].
    repeat split; try assumption.
    apply subset_b_iff_incl. exact Hpb.
  - intros [r [Hin [Heq Hsub]]]. exists r. split; [exact Hin |].
    unfold producible_by.
    destruct (Part_eq_dec (output r) p) as [Eq | NEq]; [|contradiction].
    apply subset_b_iff_incl. exact Hsub.
Qed.

(* ========================================================================== *)
(* 4. The step operator.                                                      *)
(* ========================================================================== *)

(* step C S retains exactly those parts of S which are producible from S      *)
(* using catalog C. This is the operator whose greatest fixed point on        *)
(* the powerset of S is the closure.                                          *)

Definition step (C : Catalog) (S : list Part) : list Part :=
  filter (fun p => producible C S p) S.

Lemma step_incl : forall C S, incl (step C S) S.
Proof.
  intros C S p Hin. unfold step in Hin.
  apply filter_In in Hin. tauto.
Qed.

Lemma step_monotone : forall C S T,
  incl S T -> incl (step C S) (step C T).
Proof.
  intros C S T Hsub p Hin. unfold step in *.
  apply filter_In in Hin. destruct Hin as [HinS Hprod].
  apply filter_In. split.
  - apply Hsub. exact HinS.
  - apply producible_correct in Hprod. apply producible_correct.
    destruct Hprod as [r [HrC [Hreq Hrin]]].
    exists r. repeat split; try assumption.
    intros i Hi. apply Hsub. apply Hrin. exact Hi.
Qed.

Lemma step_length_le : forall C S, length (step C S) <= length S.
Proof. intros. apply filter_length_le. Qed.

(* ========================================================================== *)
(* 5. Filter helper lemmas (no admits).                                       *)
(* ========================================================================== *)

Lemma filter_length_eq_iff_filter_eq :
  forall (A : Type) (f : A -> bool) (L : list A),
    length (filter f L) = length L <-> filter f L = L.
Proof.
  intros A f L. split.
  - intros Hlen.
    induction L as [|y rest IH]; [reflexivity|].
    cbn in Hlen. cbn.
    destruct (f y) eqn:Efy.
    + cbn in Hlen. injection Hlen as Hlen'.
      f_equal. apply IH. exact Hlen'.
    + cbn in Hlen.
      pose proof (filter_length_le f rest). lia.
  - intros Hfilter. rewrite Hfilter. reflexivity.
Qed.

Lemma filter_eq_implies_forall_true :
  forall (A : Type) (f : A -> bool) (L : list A),
    filter f L = L -> forall x, In x L -> f x = true.
Proof.
  intros A f L Hfilter x Hin.
  induction L as [|y rest IH]; [contradiction|].
  cbn in Hfilter. cbn in Hin.
  destruct (f y) eqn:Efy.
  - injection Hfilter as Hfilter'.
    destruct Hin as [Hxy | Hxin].
    + subst y. exact Efy.
    + apply IH; assumption.
  - apply f_equal with (f := @length A) in Hfilter. cbn in Hfilter.
    pose proof (filter_length_le f rest). lia.
Qed.

Lemma forall_true_implies_filter_eq :
  forall (A : Type) (f : A -> bool) (L : list A),
    (forall x, In x L -> f x = true) -> filter f L = L.
Proof.
  intros A f L Hall.
  induction L as [|y rest IH]; [reflexivity|].
  cbn. rewrite Hall by (cbn; left; reflexivity).
  f_equal. apply IH. intros x Hin. apply Hall. cbn. right. exact Hin.
Qed.

(* ========================================================================== *)
(* 6. Closure operator (bounded iteration on length S).                       *)
(* ========================================================================== *)

(* The closure is computed by iterating step until the length stabilizes.     *)
(* Since length is non-increasing and bounded below by zero, stabilization    *)
(* occurs within at most |S| iterations. The structural recursion is on the   *)
(* iteration counter, which we instantiate to length S in the definition of   *)
(* closure.                                                                   *)

Fixpoint closure_n (n : nat) (C : Catalog) (S : list Part) : list Part :=
  match n with
  | 0 => S
  | Datatypes.S n' =>
      let S' := step C S in
      if Nat.eqb (length S') (length S) then S
      else closure_n n' C S'
  end.

Definition closure (C : Catalog) (S : list Part) : list Part :=
  closure_n (length S) C S.

(* ========================================================================== *)
(* 7. Closure properties.                                                     *)
(* ========================================================================== *)

Lemma closure_n_incl : forall n C S, incl (closure_n n C S) S.
Proof.
  induction n as [|n' IH]; intros C S; cbn.
  - apply incl_refl.
  - destruct (Nat.eqb (length (step C S)) (length S)) eqn:E.
    + apply incl_refl.
    + eapply incl_tran; [apply IH | apply step_incl].
Qed.

Theorem closure_incl : forall C S, incl (closure C S) S.
Proof. intros. apply closure_n_incl. Qed.

Lemma closure_n_fixpoint : forall n C S,
  length S <= n -> step C (closure_n n C S) = closure_n n C S.
Proof.
  induction n as [|n' IH]; intros C S Hle.
  - assert (Hsze : length S = 0) by lia.
    apply length_zero_iff_nil in Hsze. subst S. reflexivity.
  - cbn. destruct (Nat.eqb (length (step C S)) (length S)) eqn:E.
    + apply Nat.eqb_eq in E.
      apply filter_length_eq_iff_filter_eq. exact E.
    + apply Nat.eqb_neq in E.
      pose proof (step_length_le C S) as Hle'.
      apply IH. lia.
Qed.

Theorem closure_fixpoint : forall C S,
  step C (closure C S) = closure C S.
Proof.
  intros. unfold closure. apply closure_n_fixpoint. lia.
Qed.

Definition closed (C : Catalog) (S : list Part) : Prop :=
  forall p, In p S -> producible C S p = true.

Lemma closed_iff_step_eq : forall C S,
  closed C S <-> step C S = S.
Proof.
  intros C S. unfold closed, step. split.
  - apply forall_true_implies_filter_eq.
  - apply filter_eq_implies_forall_true.
Qed.

Theorem closure_is_closed : forall C S, closed C (closure C S).
Proof.
  intros. apply closed_iff_step_eq. apply closure_fixpoint.
Qed.

(* Soundness: every part of the closure has a witnessing recipe whose        *)
(* inputs all lie in the closure.                                             *)

Theorem closure_sound : forall C S p,
  In p (closure C S) ->
  exists r, In r C /\ output r = p /\ incl (inputs r) (closure C S).
Proof.
  intros C S p H.
  apply producible_correct.
  apply (closure_is_closed C S). exact H.
Qed.

Lemma closure_n_maximal : forall n C S S',
  incl S' S -> step C S' = S' -> incl S' (closure_n n C S).
Proof.
  induction n as [|n' IH]; intros C S S' Hsub Hcl; cbn.
  - exact Hsub.
  - destruct (Nat.eqb (length (step C S)) (length S)) eqn:E.
    + exact Hsub.
    + apply IH.
      * intros p Hin.
        assert (Hp : In p (step C S')) by (rewrite Hcl; exact Hin).
        apply (step_monotone C S' S Hsub). exact Hp.
      * exact Hcl.
Qed.

(* Maximality: any closed subset of S is contained in the closure of S.      *)

Theorem closure_maximal : forall C S S',
  incl S' S -> closed C S' -> incl S' (closure C S).
Proof.
  intros C S S' Hsub Hcl. apply closed_iff_step_eq in Hcl.
  unfold closure. apply closure_n_maximal; assumption.
Qed.

Theorem closure_idempotent : forall C S,
  closure C (closure C S) = closure C S.
Proof.
  intros C S.
  unfold closure at 1.
  remember (closure C S) as S0 eqn:HS0.
  assert (Hfix : step C S0 = S0) by (subst S0; apply closure_fixpoint).
  assert (Hclosure_const : forall n, closure_n n C S0 = S0).
  { induction n as [|n' IH]; cbn; [reflexivity|].
    rewrite Hfix. rewrite Nat.eqb_refl. reflexivity. }
  apply Hclosure_const.
Qed.

Theorem closure_monotone : forall C S T,
  incl S T -> incl (closure C S) (closure C T).
Proof.
  intros C S T HST. apply closure_maximal.
  - eapply incl_tran; [apply closure_incl | exact HST].
  - apply closure_is_closed.
Qed.

(* The three properties that characterize closure as the greatest closed     *)
(* sublist of S.                                                              *)

Theorem closure_characterization : forall C S,
  incl (closure C S) S /\
  closed C (closure C S) /\
  (forall S', incl S' S -> closed C S' -> incl S' (closure C S)).
Proof.
  intros. repeat split.
  - apply closure_incl.
  - apply closure_is_closed.
  - apply closure_maximal.
Qed.

(* ========================================================================== *)
(* 8. Decidable closedness.                                                   *)
(* ========================================================================== *)

Definition is_closed_b (C : Catalog) (S : list Part) : bool :=
  Nat.eqb (length (step C S)) (length S).

Theorem is_closed_b_correct : forall C S,
  is_closed_b C S = true <-> closed C S.
Proof.
  intros C S. unfold is_closed_b.
  rewrite Nat.eqb_eq.
  rewrite closed_iff_step_eq.
  unfold step.
  apply filter_length_eq_iff_filter_eq.
Qed.

(* ========================================================================== *)
(* 9. Negative result: parts without a producing recipe never appear in the   *)
(*    closure.                                                                *)
(* ========================================================================== *)

Theorem no_recipe_excluded : forall C S p,
  (forall r, In r C -> output r <> p) ->
  ~ In p (closure C S).
Proof.
  intros C S p Hno HI.
  apply (closure_is_closed C S) in HI.
  apply producible_correct in HI.
  destruct HI as [r [HinC [Heq _]]].
  apply (Hno r); assumption.
Qed.

(* ========================================================================== *)
(* 10. Worked example.                                                        *)
(* ========================================================================== *)

(* A small catalog modelling a metalwork bootstrap fragment.                  *)

Definition Iron    : Part := 1.
Definition Wood    : Part := 2.
Definition Coal    : Part := 3.
Definition Steel   : Part := 4.
Definition Hammer  : Part := 5.
Definition Anvil   : Part := 6.
Definition Furnace : Part := 7.

(* The full catalog: raw extraction recipes for Iron, Wood, Coal plus four    *)
(* manufacturing recipes (Steel, Hammer, Anvil, Furnace).                     *)

Definition full_catalog : Catalog := [
  mkRecipe []                       Iron;
  mkRecipe []                       Wood;
  mkRecipe []                       Coal;
  mkRecipe [Iron; Coal; Furnace]    Steel;
  mkRecipe [Steel; Wood]            Hammer;
  mkRecipe [Iron; Iron]             Anvil;
  mkRecipe [Steel; Steel; Steel]    Furnace
].

(* The partial catalog drops the Steel recipe: Steel cannot be manufactured.  *)

Definition partial_catalog : Catalog := [
  mkRecipe []                       Iron;
  mkRecipe []                       Wood;
  mkRecipe []                       Coal;
  mkRecipe [Steel; Wood]            Hammer;
  mkRecipe [Iron; Iron]             Anvil;
  mkRecipe [Steel; Steel; Steel]    Furnace
].

Definition seed : list Part :=
  [Iron; Wood; Coal; Furnace; Steel; Hammer; Anvil].

(* Under the partial catalog, no recipe outputs Steel. *)

Theorem partial_catalog_no_steel :
  forall r, In r partial_catalog -> output r <> Steel.
Proof.
  intros r Hin. cbn in Hin.
  repeat (destruct Hin as [Heq | Hin];
          [subst r; cbn; discriminate | ]); contradiction.
Qed.

(* Therefore Steel is excluded from the closure under the partial catalog.   *)

Corollary partial_drops_steel : ~ In Steel (closure partial_catalog seed).
Proof.
  apply no_recipe_excluded. apply partial_catalog_no_steel.
Qed.

(* The same argument generalizes: under the partial catalog, Hammer and       *)
(* Furnace also drop out, because both require Steel as an input and Steel    *)
(* is forbidden by the closure invariant. The closure is computable; running  *)
(* the kernel produces the literal answer.                                    *)

Eval cbv in (closure partial_catalog seed).
Eval cbv in (closure full_catalog    seed).
