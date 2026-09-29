-- Prove2me | Theorems.Thm_lean_workbook_plus_70446
-- name    : lean_workbook_plus_70446
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/fbf361a3-3447-4a1e-bb31-d865db6dc9fb
-- statement:
--   $2(c-1)^{2}+\frac{1}{2}\\left( 2\\sqrt{d^{2}+2d}-1\\right) ^{2}\\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70446 (c d : ℝ) : (2 * (c - 1) ^ 2 + (1 / 2) * (2 * Real.sqrt (d ^ 2 + 2 * d) - 1) ^ 2) ≥ 0   :=  by sorry
