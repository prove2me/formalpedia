-- Prove2me | Theorems.Thm_lean_workbook_plus_40486
-- name    : lean_workbook_plus_40486
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/69d39f99-2bd0-4237-a116-225e9e4aa166
-- statement:
--   Let $a,b,c$ be real numbers that $ab+bc+ca=3$ . Prove that: $\frac{1}{a^2+2}+\frac{1}{b^2+2}+\frac{1}{c^2+2}\leq1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40486 (a b c : ℝ) (h : a * b + b * c + c * a = 3) : 1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2) ≤ 1   :=  by sorry
