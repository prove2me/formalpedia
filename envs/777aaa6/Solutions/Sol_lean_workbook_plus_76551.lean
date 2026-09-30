-- Prove2me | solution 1 for lean_workbook_plus_76551
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:34.141991+00:00
-- url     : https://prove2.me/submissions/d2462e79-2e08-4073-96db-512d06726eea

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 + b ^ 2 = a ^ 5 + b ^ 5) : a ^ 2 + b ^ 2 ≤ 2 := by
  have h1 : 0 ≤ (a - 1) ^ 2 * (2 * a ^ 3 + 4 * a ^ 2 + 6 * a + 3) := by positivity
  have h2 : 0 ≤ (b - 1) ^ 2 * (2 * b ^ 3 + 4 * b ^ 2 + 6 * b + 3) := by positivity
  nlinarith only [hab, h1, h2]
