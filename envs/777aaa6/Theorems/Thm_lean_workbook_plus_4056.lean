-- Prove2me | Theorems.Thm_lean_workbook_plus_4056
-- name    : lean_workbook_plus_4056
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e183e78a-7ac8-4c09-a28f-f9ad8d83da4a
-- statement:
--   Prove that $a^2b^2+b^2c^2+c^2a^2 \geq a^2bc+b^2ca+c^2ab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4056 (a b c : ℝ) : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b   :=  by sorry
