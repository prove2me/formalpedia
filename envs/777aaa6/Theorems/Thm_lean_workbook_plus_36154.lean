-- Prove2me | Theorems.Thm_lean_workbook_plus_36154
-- name    : lean_workbook_plus_36154
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/76d4565c-b5e8-4721-9b9d-4afbde5a86ff
-- statement:
--   Prove that $(ab+ac+bc)^{2} \geq 3abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36154 : ∀ a b c : ℝ, (a * b + a * c + b * c) ^ 2 ≥ 3 * a * b * c * (a + b + c)   :=  by sorry
