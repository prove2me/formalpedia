-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.tailStep_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:36.893409+00:00
-- url     : https://prove2.me/submissions/4c432c52-5ad7-4818-87d7-112af88bb3cc

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_sq
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_unitSign_sq_step
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last


attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_neg
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (reverse : Bool) (v : Lattice k) (j : Fin k) :
    ‖euclidean (tailStep reverse v j)‖ ^ 2 ≤ ‖euclidean v‖ ^ 2 - 2 * |(v j : ℝ)| + 1 := by
  rw [euclidean_norm_sq, euclidean_norm_sq]
  have hj : j ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ j
  have htail : ((tailStep reverse v j j : ℤ) : ℝ) ^ 2 =
      (v j : ℝ) ^ 2 - 2 * |(v j : ℝ)| + 1 := by
    simpa [tailStep, prefixStep] using unitSign_sq_step (v j)
  calc
    ∑ i, (tailStep reverse v j i : ℝ) ^ 2 =
        (∑ i ∈ Finset.univ.erase j, (tailStep reverse v j i : ℝ) ^ 2) + (tailStep reverse v j j : ℝ) ^ 2 :=
      (Finset.sum_erase_add _ _ hj).symm
    _ ≤ (∑ i ∈ Finset.univ.erase j, (v i : ℝ) ^ 2) +
        ((v j : ℝ) ^ 2 - 2 * |(v j : ℝ)| + 1) := by
      apply add_le_add _ htail.le
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      by_cases h : precedes reverse i j
      · simpa [tailStep, prefixStep, h] using sq_nonneg (v i : ℝ)
      · simp [tailStep, prefixStep, h, hij]
    _ = (∑ i, (v i : ℝ) ^ 2) - 2 * |(v j : ℝ)| + 1 := by
      have hh := Finset.sum_erase_add (s := Finset.univ) (f := fun i : Fin k => (v i : ℝ) ^ 2) hj
      linarith
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
