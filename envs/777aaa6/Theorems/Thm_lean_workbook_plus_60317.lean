-- Prove2me | Theorems.Thm_lean_workbook_plus_60317
-- name    : lean_workbook_plus_60317
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/326f22e4-0be6-4f1e-ba00-7b31e5bedbb4
-- statement:
--   The common approach is to use telescoping sums. Let's look at the general term: the $n$ th term is $\frac{1}{n(n+1)}$ . We know that for telescoping sums to help, we need to express the general terms as a difference, so the terms can cancel out. We know that $\frac{1}{n(n+1)} = \frac{A}{n} + \frac{B}{n+1}$ for some real $A$ and $B$ . Solving, we see that $A=1$ and $B=-1$ . Now we can use telescoping sums to find our answer. We have $1/1 - 1/2 + 1/2 - 1/3 + ... +1/49 - 1/50$ . We see a lot of terms canceling out, leaving us with $1 - \frac{1}{50} = \boxed{\frac{49}{50}}$ as our answer .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60317 :
  ∑ k in (Finset.range 50), (1 : ℝ) / (k * (k + 1)) = 49 / 50   :=  by sorry
