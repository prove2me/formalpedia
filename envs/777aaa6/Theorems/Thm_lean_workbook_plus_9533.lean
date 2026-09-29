-- Prove2me | Theorems.Thm_lean_workbook_plus_9533
-- name    : lean_workbook_plus_9533
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/9c42ea2c-db5b-48dd-99a6-794dd942b497
-- statement:
--   Prove that if $a(a-b)+b(b-c)+c(c-a)=0$ then $a=b=c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9533 (a b c : ℝ) (h : a * (a - b) + b * (b - c) + c * (c - a) = 0) : a = b ∧ b = c ∧ c = a   :=  by sorry
