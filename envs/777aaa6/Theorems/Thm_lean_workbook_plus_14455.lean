-- Prove2me | Theorems.Thm_lean_workbook_plus_14455
-- name    : lean_workbook_plus_14455
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/a34f5538-1e50-4a49-b20d-128cbf5a0f3b
-- statement:
--   The following inequality is also true. Let $a,b,c$ be positive numbers . Show that $(a+b+c)(\\frac{1}{a}+\\frac{1}{b}+\\frac{1}{c})\ge 2+\frac{7(b+c)(c+a)(a+b)}{8abc}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14455 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 2 + (7 * (b + c) * (c + a) * (a + b)) / (8 * a * b * c)   :=  by sorry
