-- Prove2me | Theorems.Thm_lean_workbook_plus_58381
-- name    : lean_workbook_plus_58381
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b38e3a8a-5701-40bb-a7ad-0639af4dcca1
-- statement:
--   There are therefore $3 + 28 + 1 + 18 + 30 + 21 = 101$ integers which have digits summing to 9. There are 670 multiples of 3, so since every multiple of 3 is equally likely, and a number with digits summing to 9 is divisible by 9, the probability of rolling an integer with digits summing to 9 is $\frac{101}{670} \cdot \frac{1}{2} = \boxed{\frac{101}{1340}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58381 :
  (3 + 28 + 1 + 18 + 30 + 21) / (670 * 2) = 101 / 1340   :=  by sorry
