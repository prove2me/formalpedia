-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:50.752746+00:00
-- url     : https://prove2.me/submissions/b06d1597-4b4c-4ae7-99ce-3a0880970b92

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_mem_cube
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_normSq_ofFn
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
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableLatticeBall
open ComputableIntegers ComputableCoverData
namespace Kourovka.MetabelianEnumeration.ComputableLatticeBall
theorem _root_.solution (k R : ℕ) (v : List ℤ) : v ∈ ball k R ↔
    ∃ w : Fin k → ℤ, List.ofFn w = v ∧ (∑ i, w i ^ 2) < (R : ℤ) ^ 2 := by
  rw [ball, List.mem_filter]
  constructor
  · rintro ⟨hv, hnorm⟩
    obtain ⟨w, rfl, _⟩ := (mem_cube R k v).mp hv
    refine ⟨w, rfl, ?_⟩
    have h := of_decide_eq_true hnorm
    have h' : (normSq (List.ofFn w) : ℤ) < (R : ℤ) ^ 2 := by exact_mod_cast h
    simpa only [normSq_ofFn] using h'
  · rintro ⟨w, rfl, hnorm⟩
    refine ⟨(mem_cube R k _).mpr ⟨w, rfl, ?_⟩, ?_⟩
    · intro i
      have hi : w i ^ 2 ≤ ∑ j, w j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
      have hR : (0 : ℤ) ≤ R := Int.natCast_nonneg R
      apply abs_le.mpr
      constructor <;> nlinarith
    · apply decide_eq_true
      have h' : (normSq (List.ofFn w) : ℤ) < (R : ℤ) ^ 2 := by rwa [normSq_ofFn]
      exact_mod_cast h'
end Kourovka.MetabelianEnumeration.ComputableLatticeBall
