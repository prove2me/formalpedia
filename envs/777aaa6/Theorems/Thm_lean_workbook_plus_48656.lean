-- Prove2me | Theorems.Thm_lean_workbook_plus_48656
-- name    : lean_workbook_plus_48656
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b9efd063-c62b-4bd4-9027-1d2b38823a2a
-- statement:
--   There are 99 positive integers less than 100. Because the square root of 100 is 10, there are 9 perfect squares in this range. The desired probability is therefore the probability of choosing 2 of these 9 when choosing 2 from the 99, $\frac{\binom{9}{2}}{\binom{99}{2}}=\boxed{\frac{4}{539}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48656 :
  ((9).choose 2 / (99).choose 2 : ℚ) = 4 / 539   :=  by sorry
