-- Prove2me | Theorems.Thm_lean_workbook_plus_8245
-- name    : lean_workbook_plus_8245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/29508672-0090-46a4-b3e0-02866e5fda49
-- statement:
--   Given three positive real numbers $a,b,c$ such that following holds $a^2=b^2+bc$ , $b^2=c^2+ac$ Prove that $\frac{1}{c}=\frac{1}{a}+\frac{1}{b}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8245 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 = b^2 + b * c) (hbc : b^2 = c^2 + c * a) : 1 / c = 1 / a + 1 / b   :=  by sorry
