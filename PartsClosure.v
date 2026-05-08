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
From Stdlib Require Import Permutation.
Import ListNotations.

(* ========================================================================== *)
(* Module Type: a decidable carrier for parts.                                *)
(* ========================================================================== *)

Module Type PART.
  Parameter t : Type.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
End PART.

(* ========================================================================== *)
(* The closure development, parametric over any decidable carrier.            *)
(* ========================================================================== *)

Module Make (P : PART).

Definition Part := P.t.
Definition Part_eq_dec := P.eq_dec.

Record Recipe : Type := mkRecipe {
  inputs : list Part;
  output : Part
}.

Definition Catalog := list Recipe.

(* -------------------------------------------------------------------------- *)
(* Membership and subset on Part lists.                                       *)
(* -------------------------------------------------------------------------- *)

Fixpoint mem (x : Part) (l : list Part) : bool :=
  match l with
  | [] => false
  | y :: rest => if Part_eq_dec x y then true else mem x rest
  end.

Lemma mem_iff_In : forall (x : Part) (l : list Part),
  mem x l = true <-> In x l.
Proof.
  intros x l. induction l as [|y rest IH].
  - cbn. split. + intros H. discriminate. + intros H. destruct H.
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

(* -------------------------------------------------------------------------- *)
(* Producibility.                                                             *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* The step operator.                                                         *)
(* -------------------------------------------------------------------------- *)

Definition step (C : Catalog) (S : list Part) : list Part :=
  filter (fun p => producible C S p) S.

Lemma step_incl : forall C S, incl (step C S) S.
Proof. intros C S p Hin. apply filter_In in Hin. tauto. Qed.

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

(* -------------------------------------------------------------------------- *)
(* Filter helpers.                                                            *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* Closure operator.                                                          *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* Closure properties.                                                        *)
(* -------------------------------------------------------------------------- *)

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

Theorem closure_sound : forall C S p,
  In p (closure C S) ->
  exists r, In r C /\ output r = p /\ incl (inputs r) (closure C S).
Proof.
  intros C S p H. apply producible_correct.
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

(* -------------------------------------------------------------------------- *)
(* NoDup preservation.                                                        *)
(* -------------------------------------------------------------------------- *)

Lemma step_NoDup : forall C S, NoDup S -> NoDup (step C S).
Proof. intros. apply NoDup_filter. exact H. Qed.

Lemma closure_n_NoDup : forall n C S, NoDup S -> NoDup (closure_n n C S).
Proof.
  induction n as [|n' IH]; intros C S H; cbn.
  - exact H.
  - destruct (Nat.eqb (length (step C S)) (length S)) eqn:E.
    + exact H.
    + apply IH. apply step_NoDup. exact H.
Qed.

Theorem closure_NoDup : forall C S, NoDup S -> NoDup (closure C S).
Proof. intros. apply closure_n_NoDup. exact H. Qed.

(* -------------------------------------------------------------------------- *)
(* Permutation invariance: producibility depends only on set membership.      *)
(* -------------------------------------------------------------------------- *)

Lemma mem_perm : forall x S T,
  Permutation S T -> mem x S = mem x T.
Proof.
  intros x S T HP.
  destruct (mem x S) eqn:ES; destruct (mem x T) eqn:ET; try reflexivity.
  - apply mem_iff_In in ES. apply (Permutation_in _ HP) in ES.
    apply mem_iff_In in ES. rewrite ES in ET. discriminate.
  - apply mem_iff_In in ET. apply Permutation_sym in HP.
    apply (Permutation_in _ HP) in ET.
    apply mem_iff_In in ET. rewrite ET in ES. discriminate.
Qed.

Lemma subset_b_perm : forall L S T,
  Permutation S T -> subset_b L S = subset_b L T.
Proof.
  intros L S T HP. unfold subset_b.
  induction L as [|x rest IH]; cbn; [reflexivity|].
  rewrite (mem_perm x S T HP). rewrite IH. reflexivity.
Qed.

Lemma producible_perm : forall C S T p,
  Permutation S T -> producible C S p = producible C T p.
Proof.
  intros C S T p HP. unfold producible.
  induction C as [|r rest IH]; cbn; [reflexivity|].
  assert (Hhead : producible_by r S p = producible_by r T p).
  { unfold producible_by. destruct (Part_eq_dec (output r) p); [|reflexivity].
    apply subset_b_perm. exact HP. }
  rewrite Hhead, IH. reflexivity.
Qed.

(* The unconditional Permutation form fails because the filter predicate    *)
(* depends on the list being permuted. We prove inclusion in both directions *)
(* and combine via NoDup_Permutation to recover the operationally useful     *)
(* statement under NoDup.                                                    *)

Lemma step_perm_incl : forall C S T,
  Permutation S T -> incl (step C S) (step C T).
Proof.
  intros C S T HP p Hin.
  apply filter_In in Hin. destruct Hin as [HinS Hprod].
  apply filter_In. split.
  - apply (Permutation_in _ HP). exact HinS.
  - rewrite <- (producible_perm C S T p HP). exact Hprod.
Qed.

Theorem step_perm_NoDup : forall C S T,
  NoDup S -> NoDup T ->
  Permutation S T -> Permutation (step C S) (step C T).
Proof.
  intros C S T HndS HndT HP.
  apply NoDup_Permutation.
  - apply step_NoDup. exact HndS.
  - apply step_NoDup. exact HndT.
  - intros x. split.
    + intros H. apply (step_perm_incl C S T HP). exact H.
    + intros H. apply (step_perm_incl C T S (Permutation_sym HP)). exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Decidable closedness.                                                      *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* No-recipe exclusion.                                                       *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* Dual operator: derivable_set, the largest closed set under C.              *)
(* -------------------------------------------------------------------------- *)

Definition all_outputs (C : Catalog) : list Part :=
  nodup Part_eq_dec (map output C).

Lemma all_outputs_NoDup : forall C, NoDup (all_outputs C).
Proof. intros. apply NoDup_nodup. Qed.

Definition derivable_set (C : Catalog) : list Part :=
  closure C (all_outputs C).

Theorem derivable_set_closed : forall C, closed C (derivable_set C).
Proof. intros. apply closure_is_closed. Qed.

Theorem derivable_set_NoDup : forall C, NoDup (derivable_set C).
Proof. intros. apply closure_NoDup. apply all_outputs_NoDup. Qed.

(* Every closed set is contained in derivable_set: closed parts are outputs. *)

Theorem closed_subset_derivable : forall C X,
  closed C X -> incl X (derivable_set C).
Proof.
  intros C X HX.
  apply closure_maximal.
  - intros p Hp. apply HX in Hp. apply producible_correct in Hp.
    destruct Hp as [r [HrC [Hreq _]]].
    unfold all_outputs. apply nodup_In.
    apply in_map_iff. exists r. split; assumption.
  - exact HX.
Qed.

(* A closed superset of T exists iff T is contained in derivable_set.        *)

Theorem closed_superset_iff : forall C T,
  (exists X, closed C X /\ incl T X) <-> incl T (derivable_set C).
Proof.
  intros C T. split.
  - intros [X [HX HT]].
    eapply incl_tran; [exact HT|]. apply closed_subset_derivable. exact HX.
  - intros HT. exists (derivable_set C). split.
    + apply derivable_set_closed.
    + exact HT.
Qed.

(* The closure of any seed S is itself contained in derivable_set.           *)

Theorem closure_subset_derivable : forall C S,
  incl (closure C S) (derivable_set C).
Proof.
  intros. apply closed_subset_derivable. apply closure_is_closed.
Qed.

End Make.

(* ========================================================================== *)
(* Concrete instantiation: Part = nat.                                        *)
(* ========================================================================== *)

Module NatPart <: PART.
  Definition t := nat.
  Definition eq_dec := Nat.eq_dec.
End NatPart.

Module NC := Make NatPart.
Import NC.

(* ========================================================================== *)
(* Worked example.                                                            *)
(* ========================================================================== *)

Definition Iron    : Part := 1.
Definition Wood    : Part := 2.
Definition Coal    : Part := 3.
Definition Steel   : Part := 4.
Definition Hammer  : Part := 5.
Definition Anvil   : Part := 6.
Definition Furnace : Part := 7.

Definition full_catalog : Catalog := [
  mkRecipe []                       Iron;
  mkRecipe []                       Wood;
  mkRecipe []                       Coal;
  mkRecipe [Iron; Coal; Furnace]    Steel;
  mkRecipe [Steel; Wood]            Hammer;
  mkRecipe [Iron; Iron]             Anvil;
  mkRecipe [Steel; Steel; Steel]    Furnace
].

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

Theorem partial_catalog_no_steel :
  forall r, In r partial_catalog -> output r <> Steel.
Proof.
  intros r Hin. cbn in Hin.
  repeat (destruct Hin as [Heq | Hin];
          [subst r; cbn; discriminate | ]); contradiction.
Qed.

Corollary partial_drops_steel : ~ In Steel (closure partial_catalog seed).
Proof.
  apply no_recipe_excluded. apply partial_catalog_no_steel.
Qed.

(* The dual: derivable_set computes everything makeable from raw recipes. *)

Eval cbv in (closure partial_catalog seed).
Eval cbv in (closure full_catalog    seed).
Eval cbv in (derivable_set partial_catalog).
Eval cbv in (derivable_set full_catalog).

(* ========================================================================== *)
(* Extraction to OCaml.                                                       *)
(* ========================================================================== *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

Extraction Language OCaml.

Extraction "PartsClosure.ml"
  closure
  derivable_set
  is_closed_b
  closed_superset_iff.
