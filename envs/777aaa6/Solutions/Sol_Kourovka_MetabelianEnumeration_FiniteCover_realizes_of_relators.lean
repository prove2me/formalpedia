-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.realizes_of_relators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:24.410735+00:00
-- url     : https://prove2.me/submissions/62de75f0-f297-47b9-a9e2-c6f52c296bf5

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
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
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (R : ℕ)
    (t : Fin k → G) (A : Fin a → G)
    (h : ∀ r ∈ relators data R, FreeGroup.lift (generatorAssignment t A) r = 1) :
    Realizes data R t A := by
  constructor
  · intro i j hij
    have hr := h (rightComm (tGenerator k a i) (tGenerator k a j) *
      (aGenerator k a (data.designated i j))⁻¹) (by
        simp only [relators, List.mem_append]
        left; left
        simp only [tRelations, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
          List.mem_filter, true_and]
        exact ⟨i, j, by simpa using hij, rfl⟩)
    simpa only [map_mul, map_inv, map_rightComm, lift_tGenerator, lift_aGenerator,
      mul_inv_eq_one] using hr
  · intro i j v hv
    have hr := h (rightComm (aGenerator k a i) (conjugate (aGenerator k a j)
      (orderedWord (tGenerator k a) v))) (by
        simp only [relators, List.mem_append]
        left; right
        simp only [shortRelations, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
        exact ⟨i, j, v, (mem_latticeBallList v).mpr hv, rfl⟩)
    simpa only [map_rightComm, map_conjugate, map_orderedWord, lift_tGenerator,
      lift_aGenerator] using hr
  · intro i p hp
    have hr := h ((aGenerator k a i)⁻¹ * polynomialWord (tGenerator k a) (aGenerator k a i) p) (by
      simp only [relators, List.mem_append]
      right
      simp only [polynomialRelations, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
      exact ⟨i, p, hp, rfl⟩)
    have he : (A i)⁻¹ * polynomialWord t (A i) p = 1 := by
      simpa only [map_mul, map_inv, map_polynomialWord, lift_tGenerator, lift_aGenerator] using hr
    exact inv_mul_eq_one.mp he
end Kourovka.MetabelianEnumeration.FiniteCover
