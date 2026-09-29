-- Prove2me | Theorems.Thm_lean_workbook_plus_7170
-- name    : lean_workbook_plus_7170
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/54b1e932-f074-4755-9812-ed2e3e0f804b
-- statement:
--   Let $a,b,c>0$ Prove that $$\frac{3}{\frac{1}{a+1}+\frac{1}{b+1}+\frac{1}{c+1}}\geq 1+\frac{3}{\frac{1}{a}+\frac{1}{b}+\frac{1}{c}}$$ $$\iff$$ $$\frac{1}{\frac{1}{a+1}+\frac{1}{b+1}+\frac{1}{c+1}}-\frac{1}{\frac{1}{a}+\frac{1}{b}+\frac{1}{c}}\geq\frac{1}{3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7170 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 / (1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1))) ≥ 1 + (3 / (1 / a + 1 / b + 1 / c)) ↔ (1 / (1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1))) - (1 / (1 / a + 1 / b + 1 / c)) ≥ 1 / 3   :=  by sorry
