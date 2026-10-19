-- Prove2me | solution 1 for AbelianTargets.FixedSlots.halfGlue_joint_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:01:36.648358+00:00
-- url     : https://prove2.me/submissions/d2f96fdf-030b-409d-8bba-5ef7d4f4281a

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointHomotopyGluing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathBounds
import Definitions.Def_AT260939824_RelativePathContraction
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

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.EndpointCorrection
section
/-! Reserving the final path slot for a continuously moving endpoint. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]











theorem lipschitz_clamp_affine (c : ℝ≥0) (b : ℝ) :
    LipschitzWith c (fun u : ℝ => clampInterval ((c : ℝ)*u+b)) := by
  simpa only [one_mul,Function.comp_def] using
    lipschitz_clampInterval.comp (lipschitz_affine_le c c b (by simp))















end
end AbelianTargets.FixedSlots

end

/-! Literal seam gluing of two square families, including moving endpoints. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {Z : Type*} [MetricSpace Z]

theorem solution (F G : unitInterval × unitInterval → Z) {K L : ℝ≥0}
    (hF : LipschitzWith K F) (hG : LipschitzWith L G)
    (hmatch : ∀ u, F (1,u) = G (0,u)) : LipschitzWith (4*max K L) (halfGlue F G) := by
  have ha : LipschitzWith 2 (fun z : ℝ × unitInterval => (clampInterval (2*z.1),z.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc := (lipschitz_clamp_affine 2 0).dist_le_mul x.1 y.1
    simp only [add_zero] at hc
    change max (dist (clampInterval (2*x.1)) (clampInterval (2*y.1))) (dist x.2 y.2) ≤ _
    apply max_le
    · exact hc.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
    · have hh : dist x.2 y.2 ≤ dist x y := le_max_right _ _
      simp only [NNReal.coe_ofNat]; nlinarith [dist_nonneg (x := x) (y := y)]
  have hb : LipschitzWith 2 (fun z : ℝ × unitInterval => (clampInterval (2*z.1-1),z.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hc := (lipschitz_clamp_affine 2 (-1)).dist_le_mul x.1 y.1
    simp only [show ∀ u : ℝ, 2*u+(-1) = 2*u-1 by intro u; ring] at hc
    change max (dist (clampInterval (2*x.1-1)) (clampInterval (2*y.1-1))) (dist x.2 y.2) ≤ _
    apply max_le
    · exact hc.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
    · have hh : dist x.2 y.2 ≤ dist x y := le_max_right _ _
      simp only [NNReal.coe_ofNat]; nlinarith [dist_nonneg (x := x) (y := y)]
  have hf : LipschitzWith (2*max K L) (fun z : ℝ × unitInterval => F (clampInterval (2*z.1),z.2)) :=
    by simpa only [Function.comp_def,mul_comm] using (hF.weaken (le_max_left K L)).comp ha
  have hg : LipschitzWith (2*max K L) (fun z : ℝ × unitInterval => G (clampInterval (2*z.1-1),z.2)) :=
    by simpa only [Function.comp_def,mul_comm] using (hG.weaken (le_max_right K L)).comp hb
  have hh := lipschitz_glue_product_at _ _ hf hg (1/2) (by
    intro u
    norm_num [clampInterval]
    exact hmatch u)
  have he : LipschitzWith 1 (fun z : unitInterval × unitInterval => ((z.1 : ℝ),z.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist x y ≤ (1 : ℝ)*dist x y
    simp
  simpa only [Function.comp_def,halfGlue,halfGlueRaw,mul_one,
    show 2*(2*max K L)=4*max K L by ring] using hh.comp he
