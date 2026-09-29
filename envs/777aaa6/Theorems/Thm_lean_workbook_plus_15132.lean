-- Prove2me | Theorems.Thm_lean_workbook_plus_15132
-- name    : lean_workbook_plus_15132
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ba641839-3f96-4449-b0f1-2814da571639
-- statement:
--   The common approach is to use telescoping sums. Let's look at the general term: the $n$ th term is $\frac{1}{n(n+1)}$ . We know that for telescoping sums to help, we need to express the general terms as a difference, so the terms can cancel out. We know that $\frac{1}{n(n+1)} = \frac{A}{n} + \frac{B}{n+1}$ for some real $A$ and $B$ . Solving, we see that $A=1$ and $B=-1$ . Now we can use telescoping sums to find our answer. We have $1/1 - 1/2 + 1/2 - 1/3 + ... +1/49 - 1/50$ . We see a lot of terms canceling out, leaving us with $1 - \frac{1}{50} = \boxed{\frac{49}{50}}$ as our answer .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15132  (n : ℕ)
  (h₀ : n = 49) :
  ∑ k in Finset.Icc 1 n, (1 / (k * (k + 1))) = 49 / 50   :=  by sorry
