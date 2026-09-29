-- Prove2me | solution 1 for WorkbookRestored.plus_38361
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:57.713789+00:00
-- url     : https://prove2.me/submissions/4d1515c0-4a98-4f84-923e-204a74144597

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_38361.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b : ℝ) : |Real.cos a| + |Real.cos b| ≥ |Real.sin (a + b)|   := by
  rw [sin_add]
  calc
    |sin a * cos b + cos a * sin b| ≤ |sin a * cos b| + |cos a * sin b| := abs_add_le _ _
    _ ≤ |cos a| + |cos b| := by
      rw [abs_mul,abs_mul]
      nlinarith [abs_sin_le_one a,abs_sin_le_one b,abs_nonneg (cos a),abs_nonneg (cos b)]
#print axioms solution
