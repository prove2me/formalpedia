-- Prove2me | Theorems.Thm_lean_workbook_plus_1078
-- name    : lean_workbook_plus_1078
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ddc5938c-7b7e-4bc6-95a4-7feb9f140336
-- statement:
--   Each number is 2 times a triangular number. Therefore the sum is $2\\times\\sum_{n=1}^{100}\\frac{n(n+1)}{2}$ . The formula for the sum of the first n triangular numbers is $\binom{n+2}{3}$ . Applying this, we find that the part with the summation symbol is 171700. The whole sum is 343400.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1078 :
  ∑ k in (Finset.range 101), 2 * (k * (k + 1) / 2) = 343400   :=  by sorry
