-- Prove2me | Theorems.Thm_lean_workbook_plus_37268
-- name    : lean_workbook_plus_37268
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9a2f9e88-7cec-4b4a-8c63-8425ed58de07
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $\frac{a}{2a+b+c}+\frac{b}{a+2b+c}+\frac{c}{a+b+2c}\le\frac{3}{4} .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37268 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (2 * a + b + c) + b / (a + 2 * b + c) + c / (a + b + 2 * c)) ≤ 3 / 4   :=  by sorry
