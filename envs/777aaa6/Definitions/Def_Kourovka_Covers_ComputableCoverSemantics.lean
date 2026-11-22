-- Prove2me | Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
-- name    : Kourovka_Covers_ComputableCoverSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:13:56.86016+00:00
-- url     : https://prove2.me/theorems/ae05cdbb-8241-4e19-bf5b-c90ab80ad289
-- title:
--   Computable Cover Semantics
-- statement:
--   Definitions and structural lemmas for Computable Cover Semantics, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Covers/ComputableCoverSemantics.lean

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverData_getD_ofFn
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_mem_ball_ofFn
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_restrict_mk
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_neg_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_neg
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.lower_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.neg_mem_ball
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_nil
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_zero


set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]
theorem map_ordered (k : ℕ) (v : List ℤ) (f : FreeGroup ℕ →* G)
    (t : Fin k → G) (ht : ∀ i : Fin k, f (FreeGroup.of i.val) = t i) :
    f (ordered k v) = orderedWord t (fun i => v.getD i.val 0) := by
  rw [ordered, map_list_prod, List.map_map, ← List.map_coe_finRange (n := k)]
  simp only [← List.ofFn_eq_map, List.map_ofFn, Function.comp_def,
    map_zpow, ht, orderedWord]
theorem map_polynomial (k : ℕ) (x : FreeGroup ℕ) (p : PolynomialCode)
    (f : FreeGroup ℕ →* G) (t : Fin k → G)
    (ht : ∀ i : Fin k, f (FreeGroup.of i.val) = t i) :
    f (ComputableCoverWords.polynomial k x p) =
      polynomialWord t (f x) (decodePolynomial k p) := by
  simp only [ComputableCoverWords.polynomial, polynomialWord, decodePolynomial,
    map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro term _
  simp only [Function.comp_def, map_conjugate, map_zpow]
  cases p.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false, Bool.cond_true, map_inv,
    map_ordered k term.1 f t ht]
theorem relators_realizes (data : DatumCode) (R : ℕ) (f : FreeGroup ℕ →* G)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G)
    (ht : ∀ i, f (FreeGroup.of i.val) = t i)
    (hA : ∀ i, f (FreeGroup.of (dimension data + i.val)) = A i) :
    (∀ r ∈ ComputableCoverWords.relators data R, f r = 1) ↔
      Realizes (decode data) R t A := by
  have htm (i j : Fin (dimension data)) :
      f (tRelator (data, (i.val, j.val))) =
        rightComm (t i) (t j) * (A ((decode data).designated i j))⁻¹ := by
    simp only [tRelator, map_mul, map_inv, map_rightComm, ht]
    exact congrArg (fun x => rightComm (t i) (t j) * x⁻¹)
      (hA ((decode data).designated i j))
  have hsm (i j : Fin (alphabet data)) (v : Fin (dimension data) → ℤ) :
      f (shortRelator (data, ((i.val, j.val), List.ofFn v))) =
        rightComm (A i) (conjugate (A j) (orderedWord t v)) := by
    simp only [shortRelator, map_rightComm, map_conjugate, hA,
      map_ordered _ _ f t ht, getD_ofFn]
  have hpm (i : Fin (alphabet data)) (p : PolynomialCode) :
      f (polynomialRelator ((data, i.val), p)) =
        (A i)⁻¹ * polynomialWord t (A i) (decodePolynomial (dimension data) p) := by
    simp only [polynomialRelator, map_mul, map_inv, hA, map_polynomial _ _ p f t ht]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have hm : tRelator (data, (i.val, j.val)) ∈ ComputableCoverWords.relators data R := by
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_flatMap.mpr
        refine ⟨i.val, List.mem_range.mpr i.isLt, List.mem_map.mpr ?_⟩
        exact ⟨j.val, List.mem_filter.mpr ⟨List.mem_range.mpr j.isLt,
          decide_eq_true hij⟩, rfl⟩
      have he := h _ hm
      rw [htm] at he
      exact mul_inv_eq_one.mp he
    · intro i j v hv
      have hm : shortRelator (data, ((i.val, j.val), List.ofFn v)) ∈
          ComputableCoverWords.relators data R := by
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨i.val, List.mem_range.mpr i.isLt, List.mem_flatMap.mpr ?_⟩
        refine ⟨j.val, List.mem_range.mpr j.isLt, List.mem_map.mpr ?_⟩
        exact ⟨List.ofFn v, (ComputableLatticeBall.mem_ball_ofFn v).mpr hv, rfl⟩
      simpa only [hsm] using h _ hm
    · intro i p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hm : polynomialRelator ((data, i.val), q) ∈
          ComputableCoverWords.relators data R := by
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        exact ⟨i.val, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨q, hq, rfl⟩⟩
      have he := h _ hm
      rw [hpm] at he
      exact inv_mul_eq_one.mp he
  · intro h r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
        obtain ⟨hj, hij⟩ := List.mem_filter.mp hj
        let i' : Fin (dimension data) := ⟨i, List.mem_range.mp hi⟩
        let j' : Fin (dimension data) := ⟨j, List.mem_range.mp hj⟩
        change f (tRelator (data, (i'.val, j'.val))) = 1
        rw [htm, h.t_comm i' j' (of_decide_eq_true hij), mul_inv_cancel]
      · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
        obtain ⟨j, hj, hr⟩ := List.mem_flatMap.mp hr
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
        obtain ⟨w, rfl, hw⟩ := ComputableLatticeBall.mem_ball _ _ _ |>.mp hv
        let i' : Fin (alphabet data) := ⟨i, List.mem_range.mp hi⟩
        let j' : Fin (alphabet data) := ⟨j, List.mem_range.mp hj⟩
        change f (shortRelator (data, ((i'.val, j'.val), List.ofFn w))) = 1
        rw [hsm]
        exact h.short_comm i' j' w hw
    · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      let i' : Fin (alphabet data) := ⟨i, List.mem_range.mp hi⟩
      change f (polynomialRelator ((data, i'.val), p)) = 1
      rw [hpm, ← h.polynomial i' _ (List.mem_map.mpr ⟨p, hp, rfl⟩), inv_mul_cancel]
def codeT (data : DatumCode) (R : ℕ) (i : Fin (dimension data)) :
    MetabelianEnumeration.GroupOf (presentation data R) :=
  PresentedGroup.of (Fin.castAdd (alphabet data) i)
def codeA (data : DatumCode) (R : ℕ) (i : Fin (alphabet data)) :
    MetabelianEnumeration.GroupOf (presentation data R) :=
  PresentedGroup.of (Fin.natAdd (dimension data) i)
def naturalAssignment (data : DatumCode)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G) : FreeGroup ℕ →* G :=
  (FreeGroup.lift (generatorAssignment t A)).comp
    (ComputablePresentations.restrictGenerators (dimension data + alphabet data))
theorem naturalAssignment_t (data : DatumCode)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G) (i : Fin (dimension data)) :
    naturalAssignment data t A (FreeGroup.of i.val) = t i := by
  have hi : i.val < dimension data + alphabet data := lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  simp only [naturalAssignment, MonoidHom.comp_apply, ComputablePresentations.restrictGenerators,
    FreeGroup.lift_apply_of, dif_pos hi]
  change generatorAssignment t A (Fin.castAdd (alphabet data) i) = _
  simp [generatorAssignment]
theorem naturalAssignment_A (data : DatumCode)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G) (i : Fin (alphabet data)) :
    naturalAssignment data t A (FreeGroup.of (dimension data + i.val)) = A i := by
  have hi : dimension data + i.val < dimension data + alphabet data := Nat.add_lt_add_left i.isLt _
  simp only [naturalAssignment, MonoidHom.comp_apply, ComputablePresentations.restrictGenerators,
    FreeGroup.lift_apply_of, dif_pos hi]
  change generatorAssignment t A (Fin.natAdd (dimension data) i) = _
  simp [generatorAssignment]
def codeRealizationHom (data : DatumCode) (R : ℕ)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G)
    (h : Realizes (decode data) R t A) :
    MetabelianEnumeration.GroupOf (presentation data R) →* G :=
  PresentedGroup.toGroup (f := generatorAssignment t A) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rw [← ComputablePresentations.restrict_mk, FreeGroup.mk_toWord]
    exact (relators_realizes data R (naturalAssignment data t A) t A
      (naturalAssignment_t data t A) (naturalAssignment_A data t A)).mpr h v hv)
end Kourovka.MetabelianEnumeration.ComputableCoverSemantics


