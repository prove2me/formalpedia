-- Prove2me | Theorems.Thm_lean_workbook_plus_77080
-- name    : lean_workbook_plus_77080
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/dd147da3-23b7-484b-82ed-cc295b65b4da
-- statement:
--   Assume $a,b,c$ are positive numbers, such that $ a(1-b) = b(1-c) = c(1-a) = \dfrac14 $. Prove that $a=b=c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77080 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0)(hab : a * (1 - b) = 1 / 4) (hbc : b * (1 - c) = 1 / 4) (hca : c * (1 - a) = 1 / 4): a = b ∧ b = c ∧ c = a   :=  by sorry
