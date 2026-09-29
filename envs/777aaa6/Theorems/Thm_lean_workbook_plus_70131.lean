-- Prove2me | Theorems.Thm_lean_workbook_plus_70131
-- name    : lean_workbook_plus_70131
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ac3bf115-d125-4a71-81ba-43956e48c330
-- statement:
--   Given positive numbers $a, b, c$ . Prove that $\frac{5 a+c}{b+c}+\frac{6 b}{c+a}+\frac{5 c+a}{a+b} \geq 9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70131 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a + c) / (b + c) + 6 * b / (c + a) + (5 * c + a) / (a + b) ≥ 9   :=  by sorry
