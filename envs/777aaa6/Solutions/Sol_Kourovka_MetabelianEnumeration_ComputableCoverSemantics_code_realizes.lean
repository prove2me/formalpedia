-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverSemantics.code_realizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:54.272349+00:00
-- url     : https://prove2.me/submissions/e033932f-c4a4-4228-9358-39174efa120c

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
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
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverSemantics
open ComputableCoverData ComputableCoverWords FiniteCover
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.ComputableCoverSemantics
theorem _root_.solution (data : DatumCode) (R : ℕ) :
    Realizes (decode data) R (codeT data R) (codeA data R) := by
  let f := (PresentedGroup.mk (relations (presentation data R))).comp
    (ComputablePresentations.restrictGenerators (dimension data + alphabet data))
  have he : FreeGroup.lift (generatorAssignment (codeT data R) (codeA data R)) =
      PresentedGroup.mk (relations (presentation data R)) := by
    apply FreeGroup.ext_hom
    intro i
    cases i using Fin.addCases <;>
      simp [generatorAssignment, codeT, codeA, PresentedGroup.of] <;> rfl
  have ht : ∀ i : Fin (dimension data), f (FreeGroup.of i.val) = codeT data R i := by
    intro i
    dsimp only [f]
    rw [← he]
    exact naturalAssignment_t data _ _ i
  have hA : ∀ i : Fin (alphabet data),
      f (FreeGroup.of (dimension data + i.val)) = codeA data R i := by
    intro i
    dsimp only [f]
    rw [← he]
    exact naturalAssignment_A data _ _ i
  apply (relators_realizes data R f _ _ ht hA).mp
  intro r hr
  change PresentedGroup.mk (relations (presentation data R))
    (ComputablePresentations.restrictGenerators _ r) = 1
  rw [← FreeGroup.mk_toWord (x := r), ComputablePresentations.restrict_mk]
  apply PresentedGroup.one_of_mem
  exact List.mem_map.mpr ⟨r.toWord, List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩
end Kourovka.MetabelianEnumeration.ComputableCoverSemantics
