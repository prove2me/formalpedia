-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.checked_cover_metabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:19:17.205186+00:00
-- url     : https://prove2.me/submissions/cf52ded8-73ac-4ad6-948e-0d9a49c13b87

import Definitions.Def_Kourovka_Covers_CoverSoundness
import Definitions.Def_Kourovka_Covers_CoverMargin
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_checkMargin_correct
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
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_certified_cover_metabelian
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_cube_margin_direction
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_supportBound_ge_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_supportBound_norm
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
open Collection ConeVerifier TamenessCompactness
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k) (r : ℕ)
    (hr : checkMargin (data.polynomials.map polynomialSupport) ((1 / 2 : ℚ) ^ r) = true) :
    Metabelian (GroupOf data (coneRadius data r)) := by
  let ε : ℚ := (1 / 2) ^ r
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hC : 0 < marginConstant k r := lt_min (div_pos hε hk0) (by norm_num)
  have hD := supportBound_ge_one data
  apply certified_cover_metabelian data hk (marginConstant k r) (supportBound data)
    hC hD ((min_le_right _ _).trans hD) (supportBound_norm data)
  intro v hv
  obtain ⟨p, hp, hdir⟩ := cube_margin_direction data hk ε hε
    ((checkMargin_correct _ _).mp hr) v hv
  refine ⟨p, hp, ?_⟩
  intro term ht
  have hCle : ((marginConstant k r : ℚ) : ℝ) ≤ ((ε / k : ℚ) : ℝ) := by
    exact_mod_cast (min_le_left (ε / k) 1)
  exact (hdir term ht).trans (by nlinarith [norm_nonneg (euclidean v)])
end Kourovka.MetabelianEnumeration.FiniteCover
