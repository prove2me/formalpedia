-- Prove2me | solution 1 for lean_workbook_plus_27087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:04.155991+00:00
-- url     : https://prove2.me/submissions/09c7205d-774e-4d4d-ae5e-29e6a55eab09

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (hn : 1 < n) : (1 : ℝ) / ((n - 1) * n * (n + 1)) = 1 / 2 * (1 / (n - 1)) - 1 * (1 / n) + 1 / 2 * (1 / (n + 1)) := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hm : (0:ℝ)<(n:ℝ)-1 := by linarith
  field_simp
  ring
