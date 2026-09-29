-- Prove2me | Theorems.Thm_lean_workbook_plus_4641
-- name    : lean_workbook_plus_4641
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9d588190-fcc5-4685-a989-dd9aea128a09
-- statement:
--   The probability is equivalent to that of the number of ways to choose 2 boys times the number of ways to choose 1 girl divided by the total number of ways to choose 3 people. That is, $\frac{\binom{15}{2}\binom{10}{1}}{\binom{20}{3}}=\frac{21}{46}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4641 :
  ((15! / (2! * 13!)) * (10! / (9! * 1!))) / (20! / (17! * 3!)) = 21 / 46   :=  by sorry
