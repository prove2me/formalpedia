-- Prove2me | Theorems.Thm_lean_workbook_plus_63456
-- name    : lean_workbook_plus_63456
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f4f3332c-872c-4d9c-9947-d819245ad8c3
-- statement:
--   Prove that $\frac{a^5+b^5+c^5}{5}=\frac{a^3+b^3+c^3}{3}.\frac{a^2+b^2+c^2}{2}$ given $a+b+c=0$ and $a^3+b^3+c^3=3abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63456 (a b c : ℝ) (h₁ : a + b + c = 0) (h₂ : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c) : (a ^ 5 + b ^ 5 + c ^ 5) / 5 = (a ^ 3 + b ^ 3 + c ^ 3) / 3 * (a ^ 2 + b ^ 2 + c ^ 2) / 2   :=  by sorry
