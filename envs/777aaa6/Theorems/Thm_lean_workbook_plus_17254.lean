-- Prove2me | Theorems.Thm_lean_workbook_plus_17254
-- name    : lean_workbook_plus_17254
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/369dd1dc-1da8-40aa-a33a-ce6ea2370fd2
-- statement:
--   I think this gives $\binom{6}{0} \binom{5}{0} + \binom{6}{1} \binom{5}{1} + \binom{6}{2} \binom{5}{2} + \binom{6}{3} \binom{5}{3} + \binom{6}{4} \binom{5}{4} + \binom{6}{5} \binom{5}{5}$ $1 \cdot 1 + 6 \cdot 5 + 15 \cdot 10 + 20 \cdot 10 + 15 \cdot 5 + 6 \cdot 1 = 1+ 30 + 150 + 200 + 75 +6 = \boxed{462}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17254 :
  ∑ k in (Finset.range 6), (Nat.choose 6 k * Nat.choose 5 k) = 462   :=  by sorry
