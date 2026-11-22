-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.cone_cover_numerical_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:19.348721+00:00
-- url     : https://prove2.me/submissions/ebc4413c-7544-4a3f-89a1-9947780b4094

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_supportBound_ge_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_supportBound_norm
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_cube_margin_direction
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_checkMargin_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_dyadic_margin_search_terminates
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_neg
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (hc : ConeCover (data.polynomials.map polynomialSupport)) :
    ∃ C D : ℚ, 0 < C ∧ 1 ≤ D ∧ C ≤ D ∧
      (∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ (D : ℝ)) ∧
      (∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
        ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -(C : ℝ) * ‖euclidean v‖) := by
  obtain ⟨r, hr⟩ := dyadic_margin_search_terminates _ hc
  let ε : ℚ := (1 / 2) ^ r
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  let C : ℚ := min (ε / k) 1
  let D := supportBound data
  have hC : 0 < C := lt_min (div_pos hε hk0) (by norm_num)
  have hD : 1 ≤ D := supportBound_ge_one data
  refine ⟨C, D, hC, hD, (min_le_right _ _).trans hD, supportBound_norm data, ?_⟩
  intro v hv
  obtain ⟨p, hp, hdir⟩ := cube_margin_direction data hk ε hε
    ((checkMargin_correct _ _).mp hr) v hv
  refine ⟨p, hp, ?_⟩
  intro term ht
  have hCle : (C : ℝ) ≤ ((ε / k : ℚ) : ℝ) := by exact_mod_cast (min_le_left (ε / k) 1)
  exact (hdir term ht).trans (by nlinarith [norm_nonneg (euclidean v)])
end Kourovka.MetabelianEnumeration.FiniteCover
