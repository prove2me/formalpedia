-- Prove2me | Theorems.Thm_lean_workbook_plus_19207
-- name    : lean_workbook_plus_19207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1bba9d69-2f4d-489c-9873-489651871aa4
-- statement:
--   The probability is equivalent to that of the number of ways to choose 2 boys times the number of ways to choose 1 girl divided by the total number of ways to choose 3 people. That is, $\frac{\binom{15}{2}\binom{10}{1}}{\binom{25}{3}}=\frac{21}{46}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19207 :
  ((Nat.choose 15 2 * Nat.choose 10 1) / Nat.choose 25 3 : ℚ) = 21 / 46   :=  by sorry
