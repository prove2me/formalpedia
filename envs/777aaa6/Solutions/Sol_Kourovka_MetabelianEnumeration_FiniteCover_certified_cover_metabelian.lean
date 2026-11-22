-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.certified_cover_metabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:18.85729+00:00
-- url     : https://prove2.me/submissions/c465e1eb-71be-4b8c-9f61-637489feb11e

import Definitions.Def_Kourovka_Collection_CollectionRadius
import Definitions.Def_Kourovka_Covers_CertifiedRadius
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverSoundness
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_all_ordered_commute
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_metabelian_of_all_ordered_commute
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_group_realizes
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_group_generators
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_sq
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_neg_mem_ball
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
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_certifiedDelta_bounds
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_certifiedRadius_large
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
theorem _root_.solution {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (C D : ℚ) (hC : 0 < C) (hD : 1 ≤ D) (hCD : C ≤ D)
    (hbound : ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ (D : ℝ))
    (hdir : ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -(C : ℝ) * ‖euclidean v‖) :
    Metabelian (GroupOf data (certifiedRadius k C D)) := by
  let R := certifiedRadius k C D
  let t := groupT data R
  let A := groupA data R
  have hrel := group_realizes data R
  have hlarge := certifiedRadius_large hk hC hD hCD
  have hdelta := certifiedDelta_bounds hk hC
  have hδkr : ((certifiedDelta k C : ℚ) : ℝ) < 1 / (2 * (k : ℝ)) := by
    have hh : ((certifiedDelta k C : ℚ) : ℝ) < ((1 / (2 * (k : ℚ)) : ℚ) : ℝ) :=
      Rat.cast_lt.mpr hdelta.2.2
    simpa using hh
  have hcomm := all_ordered_commute data t A hk C D R (certifiedDelta k C)
    (by exact_mod_cast hC) (by exact_mod_cast hlarge.1) (by exact_mod_cast hlarge.2.1)
    (by exact_mod_cast hlarge.2.2.1) (by exact_mod_cast hlarge.2.2.2)
    (by exact_mod_cast hdelta.1) (by exact_mod_cast hdelta.2.1) hδkr
    hrel.t_comm (by
      intro p q v hv
      apply (rightComm_eq_one_iff _ _).mp
      apply hrel.short_comm
      have hv2 : (∑ i, (v i : ℝ) ^ 2) < (R : ℝ) ^ 2 := by
        rw [← euclidean_norm_sq]
        change ‖euclidean v‖ < R at hv
        nlinarith [norm_nonneg (euclidean v)]
      exact_mod_cast hv2) hrel.polynomial hbound hdir
  exact metabelian_of_all_ordered_commute data t A hrel.t_comm hcomm (group_generators data R)
end Kourovka.MetabelianEnumeration.FiniteCover
