-- Prove2me | solution 1 for lean_workbook_plus_196
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-03-11T17:28:39.137259+00:00
-- url     : https://prove2.me/submissions/14ca10ca-adfc-4b96-bff4-96c28a2d1347

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution : a + b = 0 → a^2 + b^2 = -2 * a * b := by
  intro h
  have : b = -a := by linarith
  subst this
  ring

-- Auto-generated type check: solution must match the target
theorem _type_check_target : a + b = 0 → a^2 + b^2 = -2 * a * b   := by apply solution
