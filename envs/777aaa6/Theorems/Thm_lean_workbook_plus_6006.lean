-- Prove2me | Theorems.Thm_lean_workbook_plus_6006
-- name    : lean_workbook_plus_6006
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/23cc12e5-561a-435f-8e6b-a0a7396b0b82
-- statement:
--   There are a total of $\binom{10+3-1}{3-1}=\binom{12}{2}=66$ ways to split the candy. The number of ways to split the candy so that each person gets one is equal to $\binom{7+3-1}{3-1}=\binom{9}{2}=36$ ways. So, the probability that each child receives at least one piece of candy is equal to $\frac{36}{66}=\boxed{\frac{6}{11}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6006 (Nat.choose 9 2)/(Nat.choose 12 2) = 6/11   :=  by sorry
