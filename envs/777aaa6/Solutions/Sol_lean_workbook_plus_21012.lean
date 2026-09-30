-- Prove2me | solution 1 for lean_workbook_plus_21012
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:10.561269+00:00
-- url     : https://prove2.me/submissions/43bf0d7a-7ff3-4fbc-98d9-b015206bc0cd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution (k : ℕ) : (10^(2*k)) % 11 = 1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num
