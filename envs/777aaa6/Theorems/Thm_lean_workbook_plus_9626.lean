-- Prove2me | Theorems.Thm_lean_workbook_plus_9626
-- name    : lean_workbook_plus_9626
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2d04e382-6afb-48b5-8910-6b95c0b77da1
-- statement:
--   Picking $n$ distinct digits (1-9) that are in ascending order is $\binom{9}{n}$ . Therefore, we can pick from $n=1$ to $n=9$ which is $\binom{9}{1} + \binom{9}{2} + \binom{9}{3} + \dots + \binom{9}{9}$ which is the 9th row of Pascal's minus 1. Therefore our answer is $2^9 - 1 = \boxed{511}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9626 :
  ∑ k in Finset.Icc 1 9, (Nat.choose 9 k) = 511   :=  by sorry
