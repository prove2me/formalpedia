-- Prove2me | Theorems.Thm_lean_workbook_plus_54346
-- name    : lean_workbook_plus_54346
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/23e8d65f-8605-42f9-8910-9dad1afe290f
-- statement:
--   Let $a,b,c$ be positive real numbers .Prove that \n\n $$(a+b)^2+(a+b+c)^2\geq \frac{100abc}{4a+4b+c}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54346 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 + (a + b + c) ^ 2 ≥ 100 * a * b * c / (4 * a + 4 * b + c)   :=  by sorry
