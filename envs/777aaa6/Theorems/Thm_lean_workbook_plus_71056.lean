-- Prove2me | Theorems.Thm_lean_workbook_plus_71056
-- name    : lean_workbook_plus_71056
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/568ec936-df0d-4afd-8d2e-82ad10af94e5
-- statement:
--   Let $ a,b,c>0$ and $\frac{1}{a\left(b+1\right)}+\frac{1}{b\left(c+1\right)}+\frac{1}{c\left(a+1\right)}= \frac{3}{2}. $ Prove that $$abc \geq1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71056 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (1 / (a * (b + 1))) + (1 / (b * (c + 1))) + (1 / (c * (a + 1))) = 3 / 2) : a * b * c ≥ 1   :=  by sorry
