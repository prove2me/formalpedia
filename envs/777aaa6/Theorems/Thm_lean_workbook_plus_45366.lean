-- Prove2me | Theorems.Thm_lean_workbook_plus_45366
-- name    : lean_workbook_plus_45366
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4a27ada3-3844-4b6d-97ed-2dfc5bfc0134
-- statement:
--   We want to determine how many of the five elements of the set are $1$ 's, $2$ 's, $3$ 's, $4$ 's, and $5$ 's, where the order is irrelevant. So, we use stars-and-bars, with $5$ stars (one for each element of the set), and $4$ bars (since we have five possibilities for each star). The answer is $\dbinom{5+4}{4} = \dbinom{9}{4} = \boxed{126}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45366 (Nat.choose 9 4) = 126   :=  by sorry
