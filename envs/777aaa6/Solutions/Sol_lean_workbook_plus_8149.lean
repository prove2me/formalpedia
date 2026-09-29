-- Prove2me | solution 1 for lean_workbook_plus_8149
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:00:00.011486+00:00
-- url     : https://prove2.me/submissions/8dcf4ee2-2578-42b5-a535-2c69653106de

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) : (n^n / (2^n)^2 : ℝ) = (n / 4)^n := by
  rw [div_pow]
  congr 1
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  norm_num
