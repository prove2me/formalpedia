-- Prove2me | Theorems.Thm_lean_workbook_plus_53247
-- name    : lean_workbook_plus_53247
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/86182410-b893-4aa5-906b-27e5cbe4b8c2
-- statement:
--   Prove the inequality \n $$\frac{a+b}{a+b+2c}+\frac{b+c}{b+c+2a}+\frac{a+c}{a+c+2b}\geq\frac{3}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53247 : ∀ a b c : ℝ, (a + b) / (a + b + 2 * c) + (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) ≥ 3 / 2   :=  by sorry
