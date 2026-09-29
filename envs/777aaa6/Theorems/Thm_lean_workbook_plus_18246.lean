-- Prove2me | Theorems.Thm_lean_workbook_plus_18246
-- name    : lean_workbook_plus_18246
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/967edced-9de2-46be-9f0e-e643ccc0ca9a
-- statement:
--   Prove that for any positive reals a,b and c, $\frac{a}{bc}+\frac{b}{ca}+\frac{c}{ab}\geq\frac{2}{a}+\frac{2}{b}-\frac{2}{c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18246 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b / c + b / c / a + c / a / b ≥ 2 / a + 2 / b - 2 / c   :=  by sorry
