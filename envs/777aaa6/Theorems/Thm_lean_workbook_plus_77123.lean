-- Prove2me | Theorems.Thm_lean_workbook_plus_77123
-- name    : lean_workbook_plus_77123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0025e781-a2db-48a3-8303-f31bf1018f84
-- statement:
--   Prove that for all positive real numbers $a,b,c$ the following inequality holds: $(a+b+c)\left(\frac1a+\frac1b+\frac1c\right)\ge\frac{4(a^2+b^2+c^2)}{ab+bc+ca}+5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77123 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) + 5   :=  by sorry
