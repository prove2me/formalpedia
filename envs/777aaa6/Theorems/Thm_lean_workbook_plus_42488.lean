-- Prove2me | Theorems.Thm_lean_workbook_plus_42488
-- name    : lean_workbook_plus_42488
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b5591b09-2276-4c82-8135-4d7eff00a8b0
-- statement:
--   Listing all the possible fractions less than one that can be formed from the set, we have: $\frac{1}{2}, \frac{1}{3}, \frac{1}{4}, \frac{1}{5}, \frac{1}{6}, \frac{2}{3}, \frac{2}{4},\frac{2}{5},\frac{2}{6},\frac{3}{4},\frac{3}{5},\frac{3}{6},\frac{4}{5},\frac{4}{6},\frac{5}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42488 {n : ℚ | n < 1 ∧ (n.den ≤ 6 ∧ n.num ≤ 6)}  =  {1/2, 1/3, 1/4, 1/5, 1/6, 2/3, 2/4, 2/5, 2/6, 3/4, 3/5, 3/6, 4/5, 4/6, 5/6}   :=  by sorry
