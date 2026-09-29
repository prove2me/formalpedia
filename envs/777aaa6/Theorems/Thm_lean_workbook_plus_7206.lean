-- Prove2me | Theorems.Thm_lean_workbook_plus_7206
-- name    : lean_workbook_plus_7206
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f90734b4-5e90-4ac8-8c9a-95d4c59d0f19
-- statement:
--   $x^5-x^2+3 \geq x^3+2 \; \Longleftrightarrow \; (x-1)^2(x+1)(x^2+x+1) \geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7206 : ∀ x : ℝ, x^5 - x^2 + 3 ≥ x^3 + 2 ↔ (x - 1)^2 * (x + 1) * (x^2 + x + 1) ≥ 0   :=  by sorry
