-- Prove2me | Theorems.Thm_lean_workbook_plus_21310
-- name    : lean_workbook_plus_21310
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1370d422-9b84-4f0d-8055-f5d8a2d66496
-- statement:
--   Prove that $1\ge{a^2+b^2+c^2}\ge{a^2b+b^2c+c^2a}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21310 : ∀ a b c : ℝ, 1 ≥ a ^ 2 + b ^ 2 + c ^ 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a   :=  by sorry
