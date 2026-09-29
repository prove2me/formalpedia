-- Prove2me | solution 1 for WorkbookRestored.plus_64837
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:07.191985+00:00
-- url     : https://prove2.me/submissions/d896de26-feab-4c5d-ae45-bcaab89dac66

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_64837.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
open Int
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x : ℝ) (hx : 0 < x) : 1 ≤ floor x + floor (1 / x)   := by
  have hx0 : 0 ≤ floor x := Int.floor_nonneg.mpr hx.le
  have hi0 : 0 ≤ floor (1 / x) := Int.floor_nonneg.mpr (by positivity)
  by_cases hx1 : 1 ≤ x
  · have hf : 1 ≤ floor x := Int.le_floor.mpr (by exact_mod_cast hx1)
    omega
  · have hi : 1 ≤ 1 / x := (one_le_div hx).mpr (le_of_lt (lt_of_not_ge hx1))
    have hf : 1 ≤ floor (1 / x) := Int.le_floor.mpr (by exact_mod_cast hi)
    omega
#print axioms solution
