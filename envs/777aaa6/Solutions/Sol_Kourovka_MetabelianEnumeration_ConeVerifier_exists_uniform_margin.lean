-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.exists_uniform_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:30.96566+00:00
-- url     : https://prove2.me/submissions/28b22e30-2dfe-4c45-955f-a38667b674d3

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_coverScore_gt_iff
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_continuous_coverScore
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_isCompact_cubeSphere
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_cubeSphere_ne_zero


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (supports : Supports n) (hc : ConeCover supports) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
      ∀ x : Fin n → ℝ, CubeSphere x →
        ∃ support ∈ supports, ∀ u ∈ support, epsilon < dot u x := by
  have hp : ∀ x ∈ {x : Fin n → ℝ | CubeSphere x}, 0 < coverScore supports x := by
    intro x hx
    exact (coverScore_gt_iff supports x 0 le_rfl (by norm_num)).mpr
      (hc x (cubeSphere_ne_zero hx))
  obtain ⟨a, ha, hbound⟩ := (isCompact_cubeSphere n).exists_forall_le'
    (continuous_coverScore supports).continuousOn hp
  refine ⟨min (a / 2) (1 / 2), lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro x hx
  apply (coverScore_gt_iff supports x _ (le_of_lt (lt_min (by linarith) (by norm_num)))
    ((min_le_right _ _).trans_lt (by norm_num))).mp
  exact (min_le_left _ _).trans_lt (by linarith [hbound x hx])
end Kourovka.MetabelianEnumeration.ConeVerifier
