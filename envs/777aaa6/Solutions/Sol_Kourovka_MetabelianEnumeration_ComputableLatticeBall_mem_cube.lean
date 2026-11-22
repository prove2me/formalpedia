-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableLatticeBall.mem_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:09.793327+00:00
-- url     : https://prove2.me/submissions/632ee5a4-ca8f-4025-97ea-0e2b6754032c

import Definitions.Def_Kourovka_Covers_ComputableCoverData
import Definitions.Def_Kourovka_Covers_ComputableLatticeBall
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableLatticeBall_mem_interval
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
theorem _root_.solution (R k : ℕ) (v : List ℤ) : v ∈ cube R k ↔
    ∃ w : Fin k → ℤ, List.ofFn w = v ∧ ∀ i, |w i| ≤ (R : ℤ) := by
  induction k generalizing v with
  | zero =>
    constructor
    · intro h
      have hv : v = [] := by simpa [cube] using h
      subst v
      exact ⟨Fin.elim0, by simp, fun i => Fin.elim0 i⟩
    · rintro ⟨w, rfl, _⟩
      simp [cube]
  | succ k ih =>
    constructor
    · intro hv
      obtain ⟨z, hz, hmap⟩ := List.mem_flatMap.mp hv
      obtain ⟨tail, hmem, rfl⟩ := List.mem_map.mp hmap
      obtain ⟨w, hw, hbound⟩ := (ih tail).mp hmem
      refine ⟨Fin.cons z w, ?_, ?_⟩
      · simp [List.ofFn_succ, hw]
      · intro i
        cases i using Fin.cases with
        | zero => simpa using (mem_interval R z).mp hz
        | succ i => simpa using hbound i
    · rintro ⟨w, rfl, hbound⟩
      rw [List.ofFn_succ]
      apply List.mem_flatMap.mpr
      refine ⟨w 0, (mem_interval R _).mpr (hbound 0), List.mem_map.mpr ?_⟩
      refine ⟨List.ofFn (fun i => w i.succ), (ih _).mpr ⟨fun i => w i.succ, rfl, ?_⟩, rfl⟩
      exact fun i => hbound i.succ
end Kourovka.MetabelianEnumeration.ComputableLatticeBall
