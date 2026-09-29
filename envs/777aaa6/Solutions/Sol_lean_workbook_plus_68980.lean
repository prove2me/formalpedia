-- Prove2me | solution 1 for lean_workbook_plus_68980
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:02.345088+00:00
-- url     : https://prove2.me/submissions/c273648d-928d-4dc2-a341-459bf9fb8352

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (n : ℕ) (_hn : 2 ≤ n) : (n : ℝ) / (n + 1) > (n - 1) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_lt_div_iff₀ hn (by linarith : (0 : ℝ) < n + 1)).mpr
  nlinarith
