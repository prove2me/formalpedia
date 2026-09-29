-- Prove2me | solution 1 for lean_workbook_plus_23000
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:44.454673+00:00
-- url     : https://prove2.me/submissions/7dbe5b93-19bc-49f4-bdc3-c727adb8e4c6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution :  ∀ a b c : ℝ, a = b ∧ c = -2 * a + 3 → (3 / 64) * (4 * a - 3) ^ 2 * (48 * a ^ 2 - 104 * a + 57) ≥ 0 := by
  intro a b c h
  have hq : 0≤48*a^2-104*a+57 := by nlinarith only [sq_nonneg (a-13/12)]
  positivity
