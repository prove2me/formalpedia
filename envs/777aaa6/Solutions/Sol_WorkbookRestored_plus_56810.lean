-- Prove2me | solution 1 for WorkbookRestored.plus_56810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:24:57.921426+00:00
-- url     : https://prove2.me/submissions/38b4923f-d845-40fb-b789-9318b72e20cc

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_56810.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hbc : b ≠ c) (hca : a ≠ c) :
  Real.logb (c * b^2) a + Real.logb (a * c^2) b + Real.logb (b * a^2) c =
    Real.log a / (2 * Real.log b + Real.log c) + Real.log b / (2 * Real.log c + Real.log a) +
      Real.log c / (2 * Real.log a + Real.log b)   := by
  simp [logb, log_mul, log_div, hab, hbc, hca, ha.ne', hb.ne', hc.ne', add_comm, add_left_comm]
#print axioms solution
