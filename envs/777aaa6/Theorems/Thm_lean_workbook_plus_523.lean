-- Prove2me | Theorems.Thm_lean_workbook_plus_523
-- name    : lean_workbook_plus_523
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c0b8a1f9-742c-4bb1-b2e3-757163a7e40f
-- statement:
--   Given that $ y=\frac{x^{2} + x + 1}{(x-1)^{2}}$ , prove that $ y\ge\frac{1}{4}$ for all $ x\neq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_523 : ∀ x : ℝ, x ≠ 1 → (x^2 + x + 1) / (x - 1) ^ 2 ≥ 1 / 4   :=  by sorry
