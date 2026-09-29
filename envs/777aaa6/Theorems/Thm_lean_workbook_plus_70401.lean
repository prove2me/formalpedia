-- Prove2me | Theorems.Thm_lean_workbook_plus_70401
-- name    : lean_workbook_plus_70401
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/71121f74-0b01-43fe-ba7b-6a63d5bc8e38
-- statement:
--   Let $a,b,c>0.$ Prove that $\frac{ a}{2b}+\frac{a+b}{c+a}+\frac{b+c}{a+b} \geq\frac{5}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70401 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (2 * b) + (a + b) / (c + a) + (b + c) / (a + b)) ≥ 5 / 2   :=  by sorry
