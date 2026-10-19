-- Prove2me | solution 1 for AbelianTargets.FixedSlots.BottomSpliceData.family_joint_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:02:56.375983+00:00
-- url     : https://prove2.me/submissions/b6a62f7c-10a9-4757-a400-fa5bcadc948b

import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_RowSlotScaling
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_AbelianTargets_FixedSlots_correctedCarry_joint_lipschitz
import Theorems.Thm_AbelianTargets_FixedSlots_halfGlue_joint_lipschitz
import Theorems.Thm_AbelianTargets_FixedSlots_rowFamily_joint_lipschitz

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.BottomEdgeSplice
section
/-! The complete moving-endpoint family across one bottom edge. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem upperHalf_lipschitz : LipschitzWith 1 upperHalf := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  change |((r : ℝ)+1)/2-((s : ℝ)+1)/2| ≤ (1 : ℝ)*|(r : ℝ)-(s : ℝ)|
  rw [show ((r : ℝ)+1)/2-((s : ℝ)+1)/2 = ((r : ℝ)-(s : ℝ))/2 by ring,
    abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2),one_mul]
  nlinarith [abs_nonneg ((r : ℝ)-(s : ℝ))]







namespace BottomSpliceData
variable {n : ℕ} {base p q : E} {S : Set E} {Δ : ℝ≥0}
variable (D : BottomSpliceData n base p q S Δ)






theorem seam_match (u : unitInterval) : D.leftFamily (1,u) = D.rightFamily (0,u) := by
  rw [leftFamily,rowFamily_one]
  have hh := correctedCarry_row_eq n D.carrySource.vertices q
    (fun r => mix p q (upperHalf r)) D.carry 0
    (fun u => D.carry.map_zero_left u) D.carrySource.target u
  have he : upperHalf 0 = halfPoint := by apply Subtype.ext; norm_num [upperHalf,halfPoint]
  rw [he] at hh
  exact hh.symm

















end BottomSpliceData
end
end AbelianTargets.FixedSlots

end

/-! The complete moving-endpoint family across one bottom edge. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace AbelianTargets.FixedSlots.BottomSpliceData
end AbelianTargets.FixedSlots.BottomSpliceData
open AbelianTargets
open AbelianTargets.FixedSlots
open AbelianTargets.FixedSlots.BottomSpliceData
variable {n : ℕ} {base p q : E} {S : Set E} {Δ : ℝ≥0}
variable (D : BottomSpliceData n base p q S Δ)

theorem solution : ∃ J : ℝ≥0, LipschitzWith J D.family := by
  obtain ⟨C,hC⟩ := D.corresponding_bound
  have hL := rowFamily_joint_lipschitz D.leftRow D.seamRow (n+1) Δ C D.left_edges D.seam_edges hC
  obtain ⟨J,hJ⟩ := D.carry_joint
  have he : LipschitzWith Δ (fun r => mix p q (upperHalf r)) := by
    simpa only [mul_one] using (mix_lipschitz p q Δ D.edge_bound).comp upperHalf_lipschitz
  obtain ⟨K,hK⟩ := correctedCarry_joint_lipschitz n D.carry q _ hJ
    (fun r => D.carry.target r) he (fun r => by
      have h := (mix_lipschitz p q Δ D.edge_bound).dist_le_mul 1 (upperHalf r)
      rw [mix_one] at h
      exact h.trans (mul_le_of_le_one_right Δ.property (interval_dist_le_one _ _)))
  exact ⟨_,halfGlue_joint_lipschitz _ _ hL hK D.seam_match⟩
