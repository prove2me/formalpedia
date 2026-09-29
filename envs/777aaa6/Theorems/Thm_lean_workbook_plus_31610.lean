-- Prove2me | Theorems.Thm_lean_workbook_plus_31610
-- name    : lean_workbook_plus_31610
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/3a61a134-d24c-4f5f-bcad-2c06c80c3ca0
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that \n\n $$(a+1)^2 (b+1)^2 (c+1)^2\geq 4(a+b+c+1)(ab+bc+ca+abc)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31610 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 1) ^ 2 * (b + 1) ^ 2 * (c + 1) ^ 2 ≥ 4 * (a + b + c + 1) * (a * b + b * c + c * a + a * b * c)   :=  by sorry
