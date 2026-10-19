-- Prove2me | solution 1 for AbelianTargets.FixedSlots.intervalGlue_joint_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:03:05.508613+00:00
-- url     : https://prove2.me/submissions/7b554b16-9fa1-4590-ae84-adceb47fc8c0

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FiniteIntervalGluing
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

-- Preserved source skeleton: AbelianTargets.FiniteIntervalGluing
section
/-! Finite families on neighboring unit intervals glue literally.
Their path-time Lipschitz constant is independent of the number of intervals. -/

namespace AbelianTargets.FixedSlots
open scoped NNReal
noncomputable section
variable {Z : Type*} [MetricSpace Z]



theorem intervalGlue_right (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (u : unitInterval) : intervalGlue F n ((n : ℝ)+1,u) = F n (1,u) := by
  cases n with
  | zero => simp [intervalGlue,clampInterval]
  | succ n =>
    simp only [intervalGlue]
    rw [if_neg (by push_cast; linarith)]
    have he : ((n+1 : ℕ) : ℝ)+1-((n : ℝ)+1) = 1 := by push_cast; ring
    rw [he]
    simp [clampInterval]

















end
end AbelianTargets.FixedSlots

end

/-! Finite families on neighboring unit intervals glue literally.
Their path-time Lipschitz constant is independent of the number of intervals. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {Z : Type*} [MetricSpace Z]

theorem solution (F : ℕ → unitInterval × unitInterval → Z) (n : ℕ)
    (hF : ∀ i ≤ n, ∃ J : ℝ≥0, LipschitzWith J (F i))
    (hmatch : ∀ i < n, ∀ u, F i (1,u) = F (i+1) (0,u)) :
    ∃ J : ℝ≥0, LipschitzWith J (intervalGlue F n) := by
  have he : ∀ b : ℝ, LipschitzWith 1 (fun z : ℝ × unitInterval =>
      (clampInterval (z.1+b),z.2)) := by
    intro b
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change max (dist (clampInterval (x.1+b)) (clampInterval (y.1+b))) (dist x.2 y.2) ≤ _
    simp only [NNReal.coe_one,one_mul]
    apply max_le
    · have hh := (lipschitz_clamp_affine 1 b).dist_le_mul x.1 y.1
      simpa only [NNReal.coe_one,one_mul] using hh.trans (le_max_left _ _)
    · exact le_max_right _ _
  induction n with
  | zero =>
    obtain ⟨J,hJ⟩ := hF 0 le_rfl
    exact ⟨J,by simpa only [Function.comp_def,add_zero,mul_one,intervalGlue]
      using hJ.comp (he 0)⟩
  | succ n ih =>
    obtain ⟨J,hJ⟩ := ih (fun i hi => hF i (by omega)) (fun i hi => hmatch i (by omega))
    obtain ⟨L,hL⟩ := hF (n+1) le_rfl
    have hg : LipschitzWith L (fun z : ℝ × unitInterval =>
        F (n+1) (clampInterval (z.1-((n : ℝ)+1)),z.2)) := by
      simpa only [Function.comp_def,mul_one,sub_eq_add_neg] using hL.comp (he (-((n : ℝ)+1)))
    refine ⟨2*max J L,lipschitz_glue_product_at _ _
      (hJ.weaken (le_max_left J L)) (hg.weaken (le_max_right J L)) ((n : ℝ)+1) ?_⟩
    intro u
    rw [intervalGlue_right,hmatch n (by omega)]
    simp [clampInterval]
