-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ForestCountComplete
-- name    : AnalyticCombinatorics_Ch2_Mappings_ForestCountComplete
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:49:01.458738+00:00
-- url     : https://prove2.me/theorems/d2725007-06c4-4470-85bf-738092d3aa51
-- title:
--   Decomposing absorbed parent maps on a finite carrier
-- statement:
--   On an arbitrary finite carrier, roots are absorbing under a total extension of the parent map. The finite constructions record vertices whose immediate parents are roots, the remaining inner forest, choices of root parents, and correspondences between these data and the original forest. They are concrete parent-map objects and finite equivalences, without a separate undirected graph model.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/ForestCountComplete.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ForestCount
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Completing the rooted forest count

This file adds a carrier-polymorphic version of the rooted-forest definitions
from `ForestCount.lean`.  The immediate target is the depth-one decomposition:
for a forest whose root set is not all vertices, at least one non-root has a
root as parent.
-/

open scoped BigOperators

namespace AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete

noncomputable section

/-- The non-root vertices for a specified root set in an arbitrary finite carrier. -/
abbrev GNonRoot {α : Type*} (R : Finset α) : Type _ :=
  {x : α // x ∉ R}

/--
Extend a partial parent map to all vertices by fixing the roots.  Non-roots move
to their chosen parent; roots are absorbing.
-/
def Gstep {α : Type*} [DecidableEq α] (R : Finset α) (g : GNonRoot R → α) (y : α) : α :=
  if h : y ∈ R then y else g ⟨y, h⟩

/-- A vertex reaches the root set under the absorbing extension of the parent map. -/
def GReaches {α : Type*} [DecidableEq α] (R : Finset α) (g : GNonRoot R → α) (x : α) :
    Prop :=
  ∃ m : ℕ, (Gstep R g)^[m] x ∈ R

/-- Functional rooted forests with specified root set `R`, over an arbitrary finite carrier. -/
abbrev GRootedForests {α : Type*} [DecidableEq α] (R : Finset α) : Type _ :=
  {g : GNonRoot R → α // ∀ x : α, GReaches R g x}

/-- The pinned finite type instance for generalized rooted forests. -/
@[reducible] def gRootedForestsFintype {α : Type*} [DecidableEq α] [Fintype α]
    (R : Finset α) : Fintype (GRootedForests R) := by
  classical
  exact Subtype.fintype (fun g : GNonRoot R → α => ∀ x : α, GReaches R g x)

@[reducible] instance instGRootedForestsFintype {α : Type*} [DecidableEq α] [Fintype α]
    (R : Finset α) : Fintype (GRootedForests R) :=
  gRootedForestsFintype R

@[simp] lemma Gstep_of_notMem {α : Type*} [DecidableEq α] {R : Finset α}
    (g : GNonRoot R → α) {y : α} (hy : y ∉ R) :
    Gstep R g y = g ⟨y, hy⟩ := by
  simp [Gstep, hy]

lemma GReaches_of_mem {α : Type*} [DecidableEq α] {R : Finset α}
    (g : GNonRoot R → α) {x : α} (hx : x ∈ R) :
    GReaches R g x := by
  exact ⟨0, by simpa [GReaches] using hx⟩

/-- The generalized complement of a root set has the expected cardinality. -/
lemma card_gNonRoot {α : Type*} [DecidableEq α] [Fintype α] (R : Finset α) :
    Fintype.card (GNonRoot R) = Fintype.card α - R.card := by
  classical
  unfold GNonRoot
  rw [Fintype.card_subtype_compl (fun x : α => x ∈ R)]
  simp [Fintype.card_coe]

lemma gForest_parent_of_unique_nonRoot_mem_roots {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (a : GNonRoot R) (ha : ∀ x : GNonRoot R, x = a)
    (F : GRootedForests R) :
    F.1 a ∈ R := by
  classical
  by_contra hnot
  have hstep : Gstep R F.1 a.1 = a.1 := by
    simpa [Gstep, a.2] using congrArg Subtype.val (ha ⟨F.1 a, hnot⟩)
  rcases F.2 a.1 with ⟨m, hm⟩
  have hfixed : (Gstep R F.1)^[m] a.1 = a.1 :=
    Function.iterate_fixed hstep m
  exact a.2 (by simpa [hfixed] using hm)

lemma gReaches_unique_nonRoot {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (a : GNonRoot R) (ha : ∀ x : GNonRoot R, x = a) (r : R) :
    ∀ x : α, GReaches R (fun _ : GNonRoot R => (r : α)) x := by
  intro x
  by_cases hx : x ∈ R
  · exact GReaches_of_mem (fun _ : GNonRoot R => (r : α)) hx
  · have hx_eq : (⟨x, hx⟩ : GNonRoot R) = a := ha ⟨x, hx⟩
    refine ⟨1, ?_⟩
    simp [Gstep_of_notMem (fun _ : GNonRoot R => (r : α)) hx]

/-- If there is exactly one non-root vertex, a forest is determined by its root parent. -/
def gRootedForestsEquivRootsOfUniqueNonRoot {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (a : GNonRoot R) (ha : ∀ x : GNonRoot R, x = a) :
    GRootedForests R ≃ R where
  toFun F := ⟨F.1 a, gForest_parent_of_unique_nonRoot_mem_roots a ha F⟩
  invFun r := ⟨(fun _ : GNonRoot R => (r : α)), gReaches_unique_nonRoot a ha r⟩
  left_inv F := by
    apply Subtype.ext
    funext x
    have hx : x = a := ha x
    calc
      (fun _ : GNonRoot R => F.1 a) x = F.1 a := rfl
      _ = F.1 x := by rw [hx]
  right_inv r := by
    ext
    rfl

/-- The set of non-roots whose parent is a root. -/
def depthOneSet {α : Type*} [DecidableEq α] [Fintype α] {R : Finset α}
    (F : GRootedForests R) : Finset (GNonRoot R) :=
  Finset.univ.filter (fun x : GNonRoot R => F.1 x ∈ R)

@[simp] lemma mem_depthOneSet {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (x : GNonRoot R) :
    x ∈ depthOneSet F ↔ F.1 x ∈ R := by
  simp [depthOneSet]

lemma exists_depthOne_of_nonRoot {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (x : GNonRoot R) :
    ∃ y : GNonRoot R, F.1 y ∈ R := by
  classical
  let p : ℕ → Prop := fun m => (Gstep R F.1)^[m] x.1 ∈ R
  have hp : ∃ m, p m := F.2 x.1
  have hp0 : ¬ p 0 := by
    simpa [p] using x.2
  have hpos : 0 < Nat.find hp := by
    cases hzero : Nat.find hp with
    | zero =>
        exact False.elim (hp0 (by simpa [p, hzero] using Nat.find_spec hp))
    | succ m => exact Nat.succ_pos m
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hprev_not : (Gstep R F.1)^[m] x.1 ∉ R := by
    exact Nat.find_min hp (by omega)
  have hhit : (Gstep R F.1) ((Gstep R F.1)^[m] x.1) ∈ R := by
    simpa [p, hm, Function.iterate_succ_apply'] using Nat.find_spec hp
  exact ⟨⟨(Gstep R F.1)^[m] x.1, hprev_not⟩, by
    simpa [Gstep_of_notMem F.1 hprev_not] using hhit⟩

/--
The depth-one set is nonempty whenever the root set is not all of the finite
carrier.  This is the first-hit/minimal-orbit lemma needed for the sigma
decomposition.
-/
theorem depthOneSet_nonempty_of_card_lt {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (hlt : R.card < Fintype.card α) :
    (depthOneSet F).Nonempty := by
  classical
  have hnonRoot_card : 0 < Fintype.card (GNonRoot R) := by
    rw [card_gNonRoot R]
    omega
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hnonRoot_card
  rcases exists_depthOne_of_nonRoot F x with ⟨y, hy⟩
  exact ⟨y, by simpa [mem_depthOneSet] using hy⟩

/-- The target object in the depth-one decomposition. -/
abbrev DepthOneData {α : Type*} [DecidableEq α] [Fintype α] (R : Finset α) : Type _ :=
  Sigma fun S : {S : Finset (GNonRoot R) // S.Nonempty} =>
    (S.1 → R) × GRootedForests (α := GNonRoot R) S.1

/-- Reconstruct the outer parent map from depth-one data. -/
def parentOfDepthOneData {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (D : DepthOneData R) : GNonRoot R → α :=
  fun x =>
    if hx : x ∈ D.1.1 then
      (D.2.1 ⟨x, hx⟩ : α)
    else
      ((D.2.2.1 ⟨x, hx⟩ : GNonRoot R) : α)

@[simp] lemma parentOfDepthOneData_of_mem {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (D : DepthOneData R) {x : GNonRoot R} (hx : x ∈ D.1.1) :
    parentOfDepthOneData D x = (D.2.1 ⟨x, hx⟩ : α) := by
  simp [parentOfDepthOneData, hx]

@[simp] lemma parentOfDepthOneData_of_notMem {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (D : DepthOneData R) {x : GNonRoot R} (hx : x ∉ D.1.1) :
    parentOfDepthOneData D x = ((D.2.2.1 ⟨x, hx⟩ : GNonRoot R) : α) := by
  simp [parentOfDepthOneData, hx]

lemma outer_step_eq_inner_step_of_notMem_depthOneData {α : Type*}
    [DecidableEq α] [Fintype α] {R : Finset α} (D : DepthOneData R)
    {x : GNonRoot R} (hx : x ∉ D.1.1) :
    Gstep R (parentOfDepthOneData D) x.1 =
      ((Gstep D.1.1 D.2.2.1 x : GNonRoot R) : α) := by
  rw [Gstep_of_notMem (parentOfDepthOneData D) x.2]
  rw [parentOfDepthOneData_of_notMem D hx]
  rw [Gstep_of_notMem D.2.2.1 hx]

lemma outer_iterate_eq_inner_of_forall_notMem_depthOneData {α : Type*}
    [DecidableEq α] [Fintype α] {R : Finset α} (D : DepthOneData R)
    (x : GNonRoot R) :
    ∀ m : ℕ,
      (∀ j < m, (Gstep D.1.1 D.2.2.1)^[j] x ∉ D.1.1) →
        (Gstep R (parentOfDepthOneData D))^[m] x.1 =
          (((Gstep D.1.1 D.2.2.1)^[m] x : GNonRoot R) : α)
  | 0, _ => by simp
  | m + 1, hbefore => by
      have hbefore_m :
          ∀ j < m, (Gstep D.1.1 D.2.2.1)^[j] x ∉ D.1.1 := by
        intro j hj
        exact hbefore j (Nat.lt_trans hj (Nat.lt_succ_self m))
      have ih := outer_iterate_eq_inner_of_forall_notMem_depthOneData D x m hbefore_m
      have hcur : (Gstep D.1.1 D.2.2.1)^[m] x ∉ D.1.1 :=
        hbefore m (Nat.lt_succ_self m)
      calc
        (Gstep R (parentOfDepthOneData D))^[m + 1] x.1
            = Gstep R (parentOfDepthOneData D)
                ((Gstep R (parentOfDepthOneData D))^[m] x.1) := by
              rw [Function.iterate_succ_apply']
        _ = Gstep R (parentOfDepthOneData D)
                (((Gstep D.1.1 D.2.2.1)^[m] x : GNonRoot R) : α) := by
              rw [ih]
        _ = ((Gstep D.1.1 D.2.2.1)
                ((Gstep D.1.1 D.2.2.1)^[m] x) : GNonRoot R) := by
              exact outer_step_eq_inner_step_of_notMem_depthOneData D hcur
        _ = (((Gstep D.1.1 D.2.2.1)^[m + 1] x : GNonRoot R) : α) := by
              rw [Function.iterate_succ_apply']

/-- Reconstruct the outer rooted forest from depth-one data. -/
def forestOfDepthOneData {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (D : DepthOneData R) : GRootedForests R := by
  classical
  refine ⟨parentOfDepthOneData D, ?_⟩
  intro y
  by_cases hy : y ∈ R
  · exact GReaches_of_mem (parentOfDepthOneData D) hy
  · let x : GNonRoot R := ⟨y, hy⟩
    by_cases hxS : x ∈ D.1.1
    · refine ⟨1, ?_⟩
      change Gstep R (parentOfDepthOneData D) x.1 ∈ R
      rw [Gstep_of_notMem (parentOfDepthOneData D) x.2]
      rw [parentOfDepthOneData_of_mem D hxS]
      exact (D.2.1 ⟨x, hxS⟩).2
    · let q : ℕ → Prop := fun m => (Gstep D.1.1 D.2.2.1)^[m] x ∈ D.1.1
      have hq : ∃ m, q m := D.2.2.2 x
      let m := Nat.find hq
      have hqmin :
          ∀ j < m, (Gstep D.1.1 D.2.2.1)^[j] x ∉ D.1.1 := by
        intro j hj
        exact Nat.find_min hq hj
      have hiter :
          (Gstep R (parentOfDepthOneData D))^[m] y =
            (((Gstep D.1.1 D.2.2.1)^[m] x : GNonRoot R) : α) := by
        simpa [x, m] using
          outer_iterate_eq_inner_of_forall_notMem_depthOneData D x m hqmin
      have hhit : (Gstep D.1.1 D.2.2.1)^[m] x ∈ D.1.1 := by
        simpa [q, m] using Nat.find_spec hq
      have hnext :
          Gstep R (parentOfDepthOneData D)
              (((Gstep D.1.1 D.2.2.1)^[m] x : GNonRoot R) : α) ∈ R := by
        let z : GNonRoot R := (Gstep D.1.1 D.2.2.1)^[m] x
        change Gstep R (parentOfDepthOneData D) z.1 ∈ R
        rw [Gstep_of_notMem (parentOfDepthOneData D) z.2]
        rw [parentOfDepthOneData_of_mem D hhit]
        exact (D.2.1 ⟨z, hhit⟩).2
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply', hiter]
      exact hnext

/-- Restrict an outer forest to the non-depth-one non-roots. -/
def innerParentOfForest {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) :
    GNonRoot (depthOneSet F) → GNonRoot R :=
  fun x =>
    ⟨F.1 x.1, by
      intro hroot
      exact x.2 ((mem_depthOneSet F x.1).mpr hroot)⟩

@[simp] lemma innerParentOfForest_val {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (x : GNonRoot (depthOneSet F)) :
    ((innerParentOfForest F x : GNonRoot R) : α) = F.1 x.1 := rfl

lemma inner_iterate_val_eq_outer_of_forall_before_root {α : Type*}
    [DecidableEq α] [Fintype α] {R : Finset α} (F : GRootedForests R)
    (x : GNonRoot R) :
    ∀ m : ℕ,
      (∀ i ≤ m, (Gstep R F.1)^[i] x.1 ∉ R) →
        (((Gstep (depthOneSet F) (innerParentOfForest F))^[m] x : GNonRoot R) : α) =
          (Gstep R F.1)^[m] x.1
  | 0, _ => by simp
  | m + 1, hbefore => by
      have hbefore_m :
          ∀ i ≤ m, (Gstep R F.1)^[i] x.1 ∉ R := by
        intro i hi
        exact hbefore i (Nat.le_trans hi (Nat.le_succ m))
      have ih := inner_iterate_val_eq_outer_of_forall_before_root F x m hbefore_m
      let z : GNonRoot R := (Gstep (depthOneSet F) (innerParentOfForest F))^[m] x
      have hz_outer : (z : α) = (Gstep R F.1)^[m] x.1 := by
        simpa [z] using ih
      have hFz_eq :
          F.1 z = (Gstep R F.1)^[m + 1] x.1 := by
        calc
          F.1 z = Gstep R F.1 z.1 := by
            rw [Gstep_of_notMem F.1 z.2]
          _ = Gstep R F.1 ((Gstep R F.1)^[m] x.1) := by
            rw [hz_outer]
          _ = (Gstep R F.1)^[m + 1] x.1 := by
            rw [Function.iterate_succ_apply']
      have hFz_not : F.1 z ∉ R := by
        simpa [hFz_eq] using hbefore (m + 1) le_rfl
      have hz_notS : z ∉ depthOneSet F := by
        intro hzS
        exact hFz_not ((mem_depthOneSet F z).mp hzS)
      calc
        (((Gstep (depthOneSet F) (innerParentOfForest F))^[m + 1] x : GNonRoot R) : α)
            =
            ((Gstep (depthOneSet F) (innerParentOfForest F) z : GNonRoot R) : α) := by
              simp [z, Function.iterate_succ_apply']
        _ = ((innerParentOfForest F ⟨z, hz_notS⟩ : GNonRoot R) : α) := by
              rw [Gstep_of_notMem (innerParentOfForest F) hz_notS]
        _ = F.1 z := rfl
        _ = (Gstep R F.1)^[m + 1] x.1 := hFz_eq

/-- The inner rooted forest obtained by deleting the depth-one vertices. -/
def innerForestOfForest {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) :
    GRootedForests (α := GNonRoot R) (depthOneSet F) := by
  classical
  refine ⟨innerParentOfForest F, ?_⟩
  intro x
  by_cases hxS : x ∈ depthOneSet F
  · exact GReaches_of_mem (innerParentOfForest F) hxS
  · let p : ℕ → Prop := fun m => (Gstep R F.1)^[m] x.1 ∈ R
    have hp : ∃ m, p m := F.2 x.1
    have hp0 : ¬ p 0 := by
      simpa [p] using x.2
    have hpos : 0 < Nat.find hp := by
      cases hzero : Nat.find hp with
      | zero =>
          exact False.elim (hp0 (by simpa [p, hzero] using Nat.find_spec hp))
      | succ m => exact Nat.succ_pos m
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    have hbefore :
        ∀ i ≤ m, (Gstep R F.1)^[i] x.1 ∉ R := by
      intro i hi
      exact Nat.find_min hp (by omega)
    have hiter :
        (((Gstep (depthOneSet F) (innerParentOfForest F))^[m] x : GNonRoot R) : α) =
          (Gstep R F.1)^[m] x.1 :=
      inner_iterate_val_eq_outer_of_forall_before_root F x m hbefore
    let z : GNonRoot R := (Gstep (depthOneSet F) (innerParentOfForest F))^[m] x
    have hz_outer : (z : α) = (Gstep R F.1)^[m] x.1 := by
      simpa [z] using hiter
    have hFz_eq :
        F.1 z = (Gstep R F.1)^[m + 1] x.1 := by
      calc
        F.1 z = Gstep R F.1 z.1 := by
          rw [Gstep_of_notMem F.1 z.2]
        _ = Gstep R F.1 ((Gstep R F.1)^[m] x.1) := by
          rw [hz_outer]
        _ = (Gstep R F.1)^[m + 1] x.1 := by
          rw [Function.iterate_succ_apply']
    have hFz_mem : F.1 z ∈ R := by
      simpa [hFz_eq, hm] using Nat.find_spec hp
    refine ⟨m, ?_⟩
    exact (mem_depthOneSet F z).mpr hFz_mem

/-- Extract the depth-one data from an outer forest. -/
def depthOneDataOfForest {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (hlt : R.card < Fintype.card α) (F : GRootedForests R) :
    DepthOneData R :=
  ⟨⟨depthOneSet F, depthOneSet_nonempty_of_card_lt F hlt⟩,
    (fun x => ⟨F.1 x.1, (mem_depthOneSet F x.1).mp x.2⟩),
    innerForestOfForest F⟩

lemma depthOneSet_forestOfDepthOneData {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (D : DepthOneData R) :
    depthOneSet (forestOfDepthOneData D) = D.1.1 := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxS
    have hparent_mem : (forestOfDepthOneData D).1 x ∈ R :=
      (mem_depthOneSet (forestOfDepthOneData D) x).mp hx
    have hparent_not : (forestOfDepthOneData D).1 x ∉ R := by
      change parentOfDepthOneData D x ∉ R
      rw [parentOfDepthOneData_of_notMem D hxS]
      exact (D.2.2.1 ⟨x, hxS⟩).2
    exact hparent_not hparent_mem
  · intro hx
    apply (mem_depthOneSet (forestOfDepthOneData D) x).mpr
    change parentOfDepthOneData D x ∈ R
    rw [parentOfDepthOneData_of_mem D hx]
    exact (D.2.1 ⟨x, hx⟩).2

lemma rootParent_forestOfDepthOneData {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (D : DepthOneData R) (x : D.1.1) :
    (forestOfDepthOneData D).1 x.1 = (D.2.1 x : α) := by
  change parentOfDepthOneData D x.1 = (D.2.1 x : α)
  rw [parentOfDepthOneData_of_mem D x.2]

/-- Fixed-first-component depth-one data.  This avoids heterogeneous Sigma transport in
the counting argument. -/
abbrev FixedDepthOneData {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (S : Finset (GNonRoot R)) : Type _ :=
  (S → R) × GRootedForests (α := GNonRoot R) S

def rootParentOfForestAt {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (S : Finset (GNonRoot R))
    (hFS : depthOneSet F = S) : S → R :=
  fun x =>
    ⟨F.1 x.1, by
      have hx : x.1 ∈ depthOneSet F := by
        simp [hFS, x.2]
      exact (mem_depthOneSet F x.1).mp hx⟩

def innerParentOfForestAt {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (S : Finset (GNonRoot R))
    (hFS : depthOneSet F = S) : GNonRoot S → GNonRoot R :=
  fun x =>
    ⟨F.1 x.1, by
      intro hroot
      have hxDepth : x.1 ∈ depthOneSet F := (mem_depthOneSet F x.1).mpr hroot
      have hxS : x.1 ∈ S := by
        simpa [hFS] using hxDepth
      exact x.2 hxS⟩

@[simp] lemma innerParentOfForestAt_val {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (S : Finset (GNonRoot R))
    (hFS : depthOneSet F = S) (x : GNonRoot S) :
    ((innerParentOfForestAt F S hFS x : GNonRoot R) : α) = F.1 x.1 := rfl

lemma innerAt_iterate_val_eq_outer_of_forall_before_root {α : Type*}
    [DecidableEq α] [Fintype α] {R : Finset α} (F : GRootedForests R)
    (S : Finset (GNonRoot R)) (hFS : depthOneSet F = S) (x : GNonRoot R) :
    ∀ m : ℕ,
      (∀ i ≤ m, (Gstep R F.1)^[i] x.1 ∉ R) →
        (((Gstep S (innerParentOfForestAt F S hFS))^[m] x : GNonRoot R) : α) =
          (Gstep R F.1)^[m] x.1
  | 0, _ => by simp
  | m + 1, hbefore => by
      have hbefore_m :
          ∀ i ≤ m, (Gstep R F.1)^[i] x.1 ∉ R := by
        intro i hi
        exact hbefore i (Nat.le_trans hi (Nat.le_succ m))
      have ih := innerAt_iterate_val_eq_outer_of_forall_before_root F S hFS x m hbefore_m
      let z : GNonRoot R := (Gstep S (innerParentOfForestAt F S hFS))^[m] x
      have hz_outer : (z : α) = (Gstep R F.1)^[m] x.1 := by
        simpa [z] using ih
      have hFz_eq :
          F.1 z = (Gstep R F.1)^[m + 1] x.1 := by
        calc
          F.1 z = Gstep R F.1 z.1 := by
            rw [Gstep_of_notMem F.1 z.2]
          _ = Gstep R F.1 ((Gstep R F.1)^[m] x.1) := by
            rw [hz_outer]
          _ = (Gstep R F.1)^[m + 1] x.1 := by
            rw [Function.iterate_succ_apply']
      have hFz_not : F.1 z ∉ R := by
        simpa [hFz_eq] using hbefore (m + 1) le_rfl
      have hz_notS : z ∉ S := by
        intro hzS
        have hzDepth : z ∈ depthOneSet F := by
          simpa [hFS] using hzS
        exact hFz_not ((mem_depthOneSet F z).mp hzDepth)
      calc
        (((Gstep S (innerParentOfForestAt F S hFS))^[m + 1] x : GNonRoot R) : α)
            =
            ((Gstep S (innerParentOfForestAt F S hFS) z : GNonRoot R) : α) := by
              simp [z, Function.iterate_succ_apply']
        _ = ((innerParentOfForestAt F S hFS ⟨z, hz_notS⟩ : GNonRoot R) : α) := by
              rw [Gstep_of_notMem (innerParentOfForestAt F S hFS) hz_notS]
        _ = F.1 z := rfl
        _ = (Gstep R F.1)^[m + 1] x.1 := hFz_eq

def innerForestOfForestAt {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (S : Finset (GNonRoot R))
    (hFS : depthOneSet F = S) :
    GRootedForests (α := GNonRoot R) S := by
  classical
  refine ⟨innerParentOfForestAt F S hFS, ?_⟩
  intro x
  by_cases hxS : x ∈ S
  · exact GReaches_of_mem (innerParentOfForestAt F S hFS) hxS
  · let p : ℕ → Prop := fun m => (Gstep R F.1)^[m] x.1 ∈ R
    have hp : ∃ m, p m := F.2 x.1
    have hp0 : ¬ p 0 := by
      simpa [p] using x.2
    have hpos : 0 < Nat.find hp := by
      cases hzero : Nat.find hp with
      | zero =>
          exact False.elim (hp0 (by simpa [p, hzero] using Nat.find_spec hp))
      | succ m => exact Nat.succ_pos m
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    have hbefore :
        ∀ i ≤ m, (Gstep R F.1)^[i] x.1 ∉ R := by
      intro i hi
      exact Nat.find_min hp (by omega)
    have hiter :
        (((Gstep S (innerParentOfForestAt F S hFS))^[m] x : GNonRoot R) : α) =
          (Gstep R F.1)^[m] x.1 :=
      innerAt_iterate_val_eq_outer_of_forall_before_root F S hFS x m hbefore
    let z : GNonRoot R := (Gstep S (innerParentOfForestAt F S hFS))^[m] x
    have hz_outer : (z : α) = (Gstep R F.1)^[m] x.1 := by
      simpa [z] using hiter
    have hFz_eq :
        F.1 z = (Gstep R F.1)^[m + 1] x.1 := by
      calc
        F.1 z = Gstep R F.1 z.1 := by
          rw [Gstep_of_notMem F.1 z.2]
        _ = Gstep R F.1 ((Gstep R F.1)^[m] x.1) := by
          rw [hz_outer]
        _ = (Gstep R F.1)^[m + 1] x.1 := by
          rw [Function.iterate_succ_apply']
    have hFz_mem : F.1 z ∈ R := by
      simpa [hFz_eq, hm] using Nat.find_spec hp
    refine ⟨m, ?_⟩
    have hzDepth : z ∈ depthOneSet F := (mem_depthOneSet F z).mpr hFz_mem
    simpa [hFS] using hzDepth

def fixedDepthOneDataOfForest {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (F : GRootedForests R) (S : Finset (GNonRoot R))
    (hFS : depthOneSet F = S) : FixedDepthOneData S :=
  (rootParentOfForestAt F S hFS, innerForestOfForestAt F S hFS)

def depthOneSetSubtype {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (hlt : R.card < Fintype.card α) (F : GRootedForests R) :
    {S : Finset (GNonRoot R) // S.Nonempty} :=
  ⟨depthOneSet F, depthOneSet_nonempty_of_card_lt F hlt⟩

def forestOfFixedDepthOneData {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} {hlt : R.card < Fintype.card α}
    (T : {S : Finset (GNonRoot R) // S.Nonempty}) (D : FixedDepthOneData T.1) :
    {F : GRootedForests R // depthOneSetSubtype hlt F = T} :=
  ⟨forestOfDepthOneData ⟨T, D⟩, by
    apply Subtype.ext
    exact depthOneSet_forestOfDepthOneData ⟨T, D⟩⟩

def fixedDepthOneDataEquivFiber {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (hlt : R.card < Fintype.card α)
    (T : {S : Finset (GNonRoot R) // S.Nonempty}) :
    {F : GRootedForests R // depthOneSetSubtype hlt F = T} ≃ FixedDepthOneData T.1 where
  toFun F :=
    fixedDepthOneDataOfForest F.1 T.1 (congrArg Subtype.val F.2)
  invFun D := forestOfFixedDepthOneData T D
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change parentOfDepthOneData
        (⟨T, fixedDepthOneDataOfForest F.1 T.1 (congrArg Subtype.val F.2)⟩ :
          DepthOneData R) x = F.1.1 x
    by_cases hx : x ∈ T.1
    · rw [parentOfDepthOneData_of_mem _ hx]
      rfl
    · rw [parentOfDepthOneData_of_notMem _ hx]
      rfl
  right_inv D := by
    rcases D with ⟨rootParent, inner⟩
    apply Prod.ext
    · funext x
      apply Subtype.ext
      change (forestOfDepthOneData (⟨T, (rootParent, inner)⟩ : DepthOneData R)).1 x.1 =
        (rootParent x : α)
      exact rootParent_forestOfDepthOneData (⟨T, (rootParent, inner)⟩ : DepthOneData R) x
    · apply Subtype.ext
      funext x
      apply Subtype.ext
      change parentOfDepthOneData (⟨T, (rootParent, inner)⟩ : DepthOneData R) x.1 =
        ((inner.1 x : GNonRoot R) : α)
      rw [parentOfDepthOneData_of_notMem]

def sigmaFiberEquiv {A B : Type*} (f : A → B) :
    (Sigma fun b : B => {a : A // f a = b}) ≃ A where
  toFun x := x.2.1
  invFun a := ⟨f a, ⟨a, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨b, a, ha⟩
    cases ha
    rfl
  right_inv _ := rfl

lemma GReaches_fin_iff_reaches {n : ℕ} (R : Finset (Fin n)) (g : NonRoot R → Fin n)
    (x : Fin n) :
    GReaches R g x ↔ Reaches R g x := by
  rfl

/-- The generalized carrier definitions specialize definitionally to the original `Fin n` ones. -/
def finRootedForestsEquivG {n : ℕ} (R : Finset (Fin n)) :
    RootedForests R ≃ GRootedForests R where
  toFun F := ⟨F.1, by
    intro x
    exact (GReaches_fin_iff_reaches R F.1 x).mpr (F.2 x)⟩
  invFun F := ⟨F.1, by
    intro x
    exact (GReaches_fin_iff_reaches R F.1 x).mp (F.2 x)⟩
  left_inv F := by
    apply Subtype.ext
    rfl
  right_inv F := by
    apply Subtype.ext
    rfl

end

end AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete


