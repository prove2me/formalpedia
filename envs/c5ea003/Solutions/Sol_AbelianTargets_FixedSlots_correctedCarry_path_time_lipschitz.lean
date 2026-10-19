-- Prove2me | solution 1 for AbelianTargets.FixedSlots.correctedCarry_path_time_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:02:23.241068+00:00
-- url     : https://prove2.me/submissions/bc64418b-09a7-4968-8398-c7c0251a3afa

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
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

/-! Reserving the final path slot for a continuously moving endpoint. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solution (n : ℕ) (F : unitInterval × unitInterval → E)
    (q : E) (e : unitInterval → E) (Δ : ℝ≥0)
    (hF : ∀ r, LipschitzWith (Δ*(n+1)) (fun u : unitInterval => F (r,u)))
    (htarget : ∀ r, F (r,1) = q) (he : ∀ r, dist q (e r) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*(n+2)) (fun u : unitInterval => correctedCarry n F q e (r,u)) := by
  have hfactor : (Δ*(n+1))*correctionScale n = Δ*(n+2) := by
    apply Subtype.ext
    change (Δ : ℝ)*((n : ℝ)+1)*(((n : ℝ)+2)/((n : ℝ)+1)) = (Δ : ℝ)*((n : ℝ)+2)
    have hne : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
  have h₀ : LipschitzWith (Δ*(n+2)) (fun u : ℝ =>
      F (r,clampInterval ((correctionScale n : ℝ)*u))) := by
    simpa only [Function.comp_def,add_zero,hfactor] using
      (hF r).comp (lipschitz_clamp_affine (correctionScale n) 0)
  have h₁ : LipschitzWith (Δ*(n+2)) (fun u : ℝ =>
      mix q (e r) (clampInterval (((n : ℝ)+2)*u-((n : ℝ)+1)))) := by
    simpa only [Function.comp_def,sub_eq_add_neg] using
      (mix_lipschitz q (e r) Δ (he r)).comp
        (lipschitz_clamp_affine (n+2) (-((n : ℝ)+1)))
  have hh := lipschitz_glue_at _ _ h₀ h₁ (correctionCut n) (by
    rw [correctionScale_cut,correction_final_zero]
    simp [clampInterval,htarget])
  simpa only [Function.comp_def,mul_one,correctedCarry,correctedCarryRaw] using
    hh.comp (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))
