-- Prove2me | Theorems.Thm_lean_workbook_plus_36300
-- name    : lean_workbook_plus_36300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/f42d576e-8aa5-4a75-a8ee-adaaff11d97b
-- statement:
--   For arbitrary positive real numbers $ a,b,c$ prove the inequality $ \frac{a}{b+2c}+\frac{b}{c+2a}+\frac{c}{a+2b}\ge 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36300 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) ≥ 1)   :=  by sorry
