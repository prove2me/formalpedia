-- Prove2me | Theorems.Thm_lean_workbook_plus_54143
-- name    : lean_workbook_plus_54143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6e125fa4-a52e-400b-b714-28bf4d6730b0
-- statement:
--   For positive a,b,c, prove that:\n\n $ \frac{a+2b}{5c+4a}+\frac{3c}{4a+4b+c}+\frac{c+2a}{a+2b+6c} \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54143 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) / (5 * c + 4 * a) + (3 * c) / (4 * a + 4 * b + c) + (c + 2 * a) / (a + 2 * b + 6 * c) ≥ 1   :=  by sorry
