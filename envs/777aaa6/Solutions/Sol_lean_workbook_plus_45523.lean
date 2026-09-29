-- Prove2me | solution 1 for lean_workbook_plus_45523
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:31.977788+00:00
-- url     : https://prove2.me/submissions/b79233cc-2914-444c-a39f-6af8fe4eda04

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℕ) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) : x^2 + y^2 + z^2 ≤ x^2 * y + y^2 * z + z^2 * x + 1 := by
  intros
  aesop (config := {maxRuleApplications := 120})
