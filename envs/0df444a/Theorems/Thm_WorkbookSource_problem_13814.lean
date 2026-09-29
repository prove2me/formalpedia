-- Prove2me | Theorems.Thm_WorkbookSource_problem_13814
-- name    : WorkbookSource.problem_13814
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:02:48.073745+00:00
-- url     : https://prove2.me/theorems/3c70dfa5-0aaa-4ff2-8bf1-594cc48d4611
-- title:
--   Translation preserves mean absolute deviation
-- statement:
--   Let's say the set is $S_{1}=[a,b,c,d]$ let $m=\frac{a+b+c+d}{4}$. From the information given, the standard deviation is the average of the differences between the elements of the set and $m$. Something like $D_{1}=\frac{1}{4}(|a-m|+|b-m|+|c-m|+|d-m|)$ and that equals 6. Now, the new set should be $S_{2}=[a+3,b+3,c+3,d+3]$ let $n=\frac{a+3+b+3+c+3+d+3}{4}=m+3$. $D_{2}=\frac{1}{4}(|a+3-(m+3)|+|b+3-(m-3)|+|c+3-(m+3)|+|d+3-(m+3)|)$. This should hold no matter how many elements the sets contain. We can see that the $3s$ cancel out so that $D_{1}=D_{2}=6$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13814` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved. The displayed absolute-deviation formula measures mean absolute deviation, although the source calls it standard deviation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13814; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13814  (a b c d m n : ℝ)
  (h₀ : m = (a + b + c + d) / 4)
  (h₁ : n = (a + 3 + b + 3 + c + 3 + d + 3) / 4)
  (h₂ : abs (a - m) + abs (b - m) + abs (c - m) + abs (d - m) = 24) :
  abs (a + 3 - n) + abs (b + 3 - n) + abs (c + 3 - n) + abs (d + 3 - n) = 24  :=  by sorry
