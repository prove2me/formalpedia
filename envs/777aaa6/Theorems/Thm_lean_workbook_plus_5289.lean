-- Prove2me | Theorems.Thm_lean_workbook_plus_5289
-- name    : lean_workbook_plus_5289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/79da75ee-83ea-4142-aea7-86cd5a82be51
-- statement:
--   For $ a,b,c>0 $ prove that:\n $ 2+\frac{a^2+b^2+c^2}{ab+bc+ca}\ge\frac{a+b}{b+c}+\frac{b+c}{c+a}+\frac{c+a}{a+b} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5289 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 + (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b)   :=  by sorry
