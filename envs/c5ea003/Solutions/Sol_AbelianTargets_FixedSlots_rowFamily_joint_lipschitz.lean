-- Prove2me | solution 1 for AbelianTargets.FixedSlots.rowFamily_joint_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:02:16.843492+00:00
-- url     : https://prove2.me/submissions/b0b72f01-cb16-4fae-aac7-2dd9d83eb210

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
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

-- Preserved source skeleton: AbelianTargets.FixedSlotInterpolation
section
/-!
# Fixed slots and the path-time estimate in Section 4

Finite rows are interpolated in fixed equal-width slots. The path-time
Lipschitz constant is simplex diameter times the slot count. It does not
depend on the number of intermediate homotopy rows. This file proves the
affine estimate and literal endpoint agreement, rather than assuming a
controlled contraction for the interval carriers.
-/

namespace AbelianTargets.FixedSlots

open scoped NNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



























/-- At every interpolation row, the same slot budget controls path-time.
The number of homotopy rows does not occur in this bound. -/
theorem interpolated_row_lipschitz (T : ℕ) (hT : 0 < T)
    (row₀ row₁ : ℕ → E) (n : ℕ) (Δ : ℝ≥0)
    (hedges₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (hedges₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*T) (rowPath T (fun j => mix (row₀ j) (row₁ j) r) n) := by
  apply rowPath_lipschitz T hT _ n Δ
  intro j hj
  exact mix_dist_le_of_le (hedges₀ j hj) (hedges₁ j hj) r































namespace BasedRow

variable {n : ℕ} {p q : E}









end BasedRow



















end

end AbelianTargets.FixedSlots

end

-- Preserved source skeleton: AbelianTargets.VariableRowFamilies
section
/-! Fixed-slot row interpolation with a moving terminal vertex. -/

namespace AbelianTargets.FixedSlots

open scoped NNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem rowFamily_path_time_lipschitz (row₀ row₁ : ℕ → E) (n : ℕ) (Δ : ℝ≥0)
    (h₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (h₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*(n+1)) (fun u : unitInterval => rowFamily row₀ row₁ n (r,u)) := by
  simpa only [mul_one,Nat.cast_add,Nat.cast_one,rowFamily,Function.comp_def] using
    (interpolated_row_lipschitz (n+1) (Nat.succ_pos n) row₀ row₁ n Δ h₀ h₁ r).comp
      (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))













end
end AbelianTargets.FixedSlots

end

/-! Fixed-slot row interpolation with a moving terminal vertex. -/
namespace AbelianTargets.FixedSlots
end AbelianTargets.FixedSlots
open AbelianTargets
open AbelianTargets.FixedSlots
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solution (row₀ row₁ : ℕ → E) (n : ℕ) (Δ C : ℝ≥0)
    (h₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (h₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ)
    (hv : ∀ j ≤ n+1, dist (row₀ j) (row₁ j) ≤ C) :
    LipschitzWith (Δ*(n+1)+C) (rowFamily row₀ row₁ n) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨r,u⟩ ⟨s,v⟩
  have hu := (rowFamily_path_time_lipschitz row₀ row₁ n Δ h₀ h₁ r).dist_le_mul u v
  have hs := interpolated_row_parameter_bound row₀ row₁ n C hv r s v
  calc
    _ ≤ dist (rowFamily row₀ row₁ n (r,u)) (rowFamily row₀ row₁ n (r,v)) +
      dist (rowFamily row₀ row₁ n (r,v)) (rowFamily row₀ row₁ n (s,v)) := dist_triangle _ _ _
    _ ≤ (Δ*(n+1) : ℝ≥0)*dist u v + C*dist r s := add_le_add hu hs
    _ ≤ (Δ*(n+1) : ℝ≥0)*dist (r,u) (s,v) + C*dist (r,u) (s,v) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) C.property)
    _ = (Δ*(n+1)+C : ℝ≥0)*dist (r,u) (s,v) := by simp [add_mul]
