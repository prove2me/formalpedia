-- Prove2me | solution 1 for AbelianTargets.FixedSlots.intervalGlue_on_unit
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:03:21.27339+00:00
-- url     : https://prove2.me/submissions/c6c202c4-162d-47b4-a0b7-d5faae235c67

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FiniteIntervalGluing
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RectangleHalfGluing
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

theorem solution (F : ℕ → unitInterval × unitInterval → Z) (N i : ℕ)
    (hi : i ≤ N) (hmatch : ∀ j < N, ∀ u, F j (1,u) = F (j+1) (0,u))
    (s u : unitInterval) : intervalGlue F N ((i : ℝ)+s,u) = F i (s,u) := by
  induction N with
  | zero =>
    have he : i = 0 := by omega
    subst i
    simp only [intervalGlue,Nat.cast_zero,zero_add,clampInterval_coe]
  | succ N ih =>
    by_cases hi' : i ≤ N
    · simp only [intervalGlue]
      rw [if_pos (by
        have hiR : (i : ℝ) ≤ N := by exact_mod_cast hi'
        linarith [s.property.2])]
      exact ih hi' (fun j hj => hmatch j (by omega))
    · have he : i = N+1 := by omega
      subst i
      by_cases hs : (s : ℝ) = 0
      · have hs' : s = 0 := Subtype.ext hs
        subst s
        simp only [intervalGlue]
        rw [if_pos (by simp),show ((N+1 : ℕ) : ℝ)+(0 : unitInterval) =
          (N : ℝ)+1 by simp,intervalGlue_right,hmatch N (by omega)]
      · simp only [intervalGlue]
        rw [if_neg (by push_cast; intro h; apply hs; linarith [s.property.1])]
        have hc : ((N+1 : ℕ) : ℝ)+(s : ℝ)-((N : ℝ)+1) = (s : ℝ) := by push_cast; ring
        rw [hc,clampInterval_coe]
