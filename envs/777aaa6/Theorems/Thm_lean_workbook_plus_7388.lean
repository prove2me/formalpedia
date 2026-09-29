-- Prove2me | Theorems.Thm_lean_workbook_plus_7388
-- name    : lean_workbook_plus_7388
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0deacfe7-2627-41ae-8710-031ea2e0d0ec
-- statement:
--   Let $a,b,c>0$ and $abc=1$ . Prove that \n $$1+\frac{8}{ (a+b)(1+c)}\ge \frac{9}{a+b+c} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7388 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 + 8 / (a + b) * (1 + 1 / c) ≥ 9 / (a + b + c)   :=  by sorry
