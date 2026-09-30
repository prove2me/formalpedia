-- Prove2me | solution 1 for lean_workbook_plus_77859
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:08.789221+00:00
-- url     : https://prove2.me/submissions/aed5d5bc-c98c-4cca-9d2b-f6b46f24fe6b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℕ → ℝ) (n : ℕ)
    (h : x (n + 1) * x n + 3 * x n - 2 * x (n + 1) - x (n + 1) ^ 2 - 2 = 0) :
    x n - 2 = (x (n + 1) + 2) * (x (n + 1) - x n) := by
  nlinarith only [h]
