-- Prove2me | Theorems.Thm_lean_workbook_plus_2357
-- name    : lean_workbook_plus_2357
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/82a4fb52-168e-482e-8127-fa88a968bc24
-- statement:
--   Let $a,b,c>0$ . Prove that \n $a,b,c>0\Longrightarrow \frac{a^{2}+b^{2}+c^{2}}{ab+bc+ac}+\frac{1}{2}\geq\sum\frac{a}{b+c} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2357 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 1 / 2 ≥ a / (b + c) + b / (c + a) + c / (a + b)   :=  by sorry
