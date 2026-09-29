-- Prove2me | solution 1 for WorkbookRestored.plus_15818
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:35:19.310225+00:00
-- url     : https://prove2.me/submissions/247bc2d2-bea3-462e-916f-e1029d3dba6d

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_15818.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  ∀ x : ℝ,
    abs (sin x + cos x) + abs (sin x - cos x) ≥ 2 * (sin x)^2   := by
  intro x
  have ht := abs_add_le (sin x + cos x) (sin x - cos x)
  have he : sin x + cos x + (sin x - cos x) = 2 * sin x := by ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  have hs : |sin x| ≤ 1 := abs_le.mpr ⟨neg_one_le_sin x, sin_le_one x⟩
  nlinarith [sq_abs (sin x), abs_nonneg (sin x)]
#print axioms solution
