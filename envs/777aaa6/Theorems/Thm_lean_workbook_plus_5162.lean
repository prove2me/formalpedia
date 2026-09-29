-- Prove2me | Theorems.Thm_lean_workbook_plus_5162
-- name    : lean_workbook_plus_5162
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/28b4f943-6d1e-4788-8260-5073265c4af3
-- statement:
--   or use induction. First of all, it is obvious to see that this sequence is twice $1 + 2 + \cdots + n$ . I claim that this sequence's sum is equal to $\frac{n(n+1)}{2}$ . This is trivially true for $n = 1$ . Now assume it true for $n-1$ --> we then get $S_{n} = S_{n-1} + n = \frac{n(n-1)}{2} +n = \frac{n(n+1)}{2}$ , so we are done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5162  (n : ℕ) :
  ∑ k in (Finset.range (n + 1)), k = n * (n + 1) / 2   :=  by sorry
