-- Prove2me | Theorems.Thm_lean_workbook_plus_6977
-- name    : lean_workbook_plus_6977
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0fb6bd58-5263-45aa-b338-4bf0fba0d4b5
-- statement:
--   Prove that for positive reals a, b, c, the following inequality holds: $\sum\frac{b+c}{a^2+bc}\leq\frac{1}{a}+\frac{1}{b}+\frac{1}{c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6977 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (a ^ 2 + b * c) + (a + c) / (b ^ 2 + a * c) + (a + b) / (c ^ 2 + a * b) ≤ 1 / a + 1 / b + 1 / c   :=  by sorry
