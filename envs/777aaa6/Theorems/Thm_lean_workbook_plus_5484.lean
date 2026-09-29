-- Prove2me | Theorems.Thm_lean_workbook_plus_5484
-- name    : lean_workbook_plus_5484
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/08cc4286-29a5-4567-8d11-9552daa779ba
-- statement:
--   Let $a,b,c>0, \frac{a}{b+c}+\frac{b}{c+a}\leq 1.$ Prove that $$\frac{c}{a+b}\geq \frac{1}{2}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5484 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) ≤ 1 → c / (a + b) ≥ 1 / 2)   :=  by sorry
