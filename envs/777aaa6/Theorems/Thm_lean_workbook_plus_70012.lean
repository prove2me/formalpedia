-- Prove2me | Theorems.Thm_lean_workbook_plus_70012
-- name    : lean_workbook_plus_70012
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/6fe3c943-545c-490c-b5f8-6a385e0f5049
-- statement:
--   Prove that $(A+B+C)^2 \geq 3(AB+BC+CA)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70012 (A B C: ℝ) : (A + B + C) ^ 2 ≥ 3 * (A * B + B * C + C * A)   :=  by sorry
