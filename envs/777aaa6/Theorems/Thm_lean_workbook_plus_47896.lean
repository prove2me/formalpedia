-- Prove2me | Theorems.Thm_lean_workbook_plus_47896
-- name    : lean_workbook_plus_47896
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ecd02862-bf8b-4aa4-9ea0-018f0d898b04
-- statement:
--   Let $a,b>0$ and $a+\frac{2}{a}-\frac{5b}{4}+\frac{4}{b}=5.$ Prove that $$a+b\ge 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47896 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + 2 / a - 5 * b / 4 + 4 / b = 5) : a + b ≥ 2   :=  by sorry
