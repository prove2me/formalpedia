-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.metabelian_of_all_ordered_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:22.694033+00:00
-- url     : https://prove2.me/submissions/cfc17577-c411-4dd9-90a5-11e38fe4472b

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_commute_hom_of_generators
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_neg_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_normalClosure_abelian
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_rightComm_eq_one_iff
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
theorem _root_.solution {k a : ℕ} (data : Datum k a)
    (t : Fin k → G) (A : Fin a → G)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) : Metabelian G := by
  let N := Subgroup.normalClosure (Set.range A)
  let f := QuotientGroup.mk' N
  have hA : ∀ i, f (A i) = 1 := by
    intro i
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i, rfl⟩)
  have htt : ∀ i j, Commute (f (t i)) (f (t j)) := by
    have hlt : ∀ i j, i < j → Commute (f (t i)) (f (t j)) := by
      intro i j hij
      apply (rightComm_eq_one_iff _ _).mp
      rw [← map_rightComm, ht i j hij, hA]
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hlt i j hij
    · exact Commute.refl _
    · exact (hlt j i hji).symm
  have hf := commute_hom_of_generators f (Set.range t ∪ Set.range A) hgen (by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact htt i j
    · simp [hA]
    · simp [hA]
    · simp [hA])
  have hmem : ∀ x y : G, ⁅x, y⁆ ∈ N := by
    intro x y
    apply (QuotientGroup.eq_one_iff _).mp
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hf x y
  intro x y z w
  exact normalClosure_abelian A t data.designated ht hs hgen _ (hmem x y) _ (hmem z w)
end Kourovka.MetabelianEnumeration.FiniteCover
