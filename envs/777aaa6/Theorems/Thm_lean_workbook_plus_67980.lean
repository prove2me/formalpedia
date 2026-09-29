-- Prove2me | Theorems.Thm_lean_workbook_plus_67980
-- name    : lean_workbook_plus_67980
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0868771e-abe7-4fc8-8ed1-b741df9a5074
-- statement:
--   We know that the number of ways to arrange the letters in a word is the factorial of the number of letters in that word, giving us $8!$ . However, because there are 2 C's and 2 A's that are not distinguishable if switched, we need to divide by their possible permutations. Therefore, the answer is $\frac{8!}{2!\cdot2!}=10080$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67980 :
  8! / (2! * 2!) = 10080   :=  by sorry
