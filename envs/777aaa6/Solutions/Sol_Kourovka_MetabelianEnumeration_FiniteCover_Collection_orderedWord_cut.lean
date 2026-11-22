-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:57:09.204183+00:00
-- url     : https://prove2.me/submissions/c4c0e90c-0c70-453a-a2f7-8003e3662ba4

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_snoc
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
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (t : Fin k → G) (v : Lattice k) (j : Fin k) (m : ℤ) :
    orderedWord t v = orderedWord t (cutLeft v j m) * orderedWord t (cutRight v j m) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    cases j using Fin.lastCases with
    | last =>
      have hl : (fun i : Fin k => cutLeft v (Fin.last k) m i.castSucc) =
          fun i => v i.castSucc := by
        ext i; simp [cutLeft]
      have hr : (fun i : Fin k => cutRight v (Fin.last k) m i.castSucc) = 0 := by
        ext i; simp [cutRight, cutLeft]
      rw [orderedWord_snoc t v, orderedWord_snoc t (cutLeft v (Fin.last k) m),
        orderedWord_snoc t (cutRight v (Fin.last k) m), hl, hr]
      simp only [orderedWord_zero, one_mul]
      simp only [cutLeft, lt_self_iff_false, ↓reduceIte, cutRight, Pi.sub_apply]
      rw [mul_assoc, ← zpow_add]
      congr 2
      omega
    | cast j =>
      have hl : (fun i : Fin k => cutLeft v j.castSucc m i.castSucc) =
          cutLeft (fun i => v i.castSucc) j m := by
        ext i; simp [cutLeft]
      have hr : (fun i : Fin k => cutRight v j.castSucc m i.castSucc) =
          cutRight (fun i => v i.castSucc) j m := by
        ext i; simp [cutRight, cutLeft]
      have hlast : cutLeft v j.castSucc m (Fin.last k) = 0 := by
        have hlt : ¬ Fin.last k < j.castSucc := not_lt_of_ge (Fin.castSucc_lt_last j).le
        have hne : Fin.last k ≠ j.castSucc := ne_of_gt (Fin.castSucc_lt_last j)
        simp [cutLeft, hlt, hne]
      rw [orderedWord_snoc t v, orderedWord_snoc t (cutLeft v j.castSucc m),
        orderedWord_snoc t (cutRight v j.castSucc m), hl, hr, hlast]
      simp only [zpow_zero, mul_one, cutRight, Pi.sub_apply, hlast, sub_zero]
      rw [ih (fun i => t i.castSucc) (fun i => v i.castSucc) j, mul_assoc]
      rfl
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
