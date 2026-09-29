-- Prove2me | Theorems.Thm_lean_workbook_plus_5982
-- name    : lean_workbook_plus_5982
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/42d29afa-f8ab-4d33-89f0-8c2019578026
-- statement:
--   Express $a, b, c$ in terms of cosines: $a = 2\cos x, b = 2\cos y, c = 2\cos z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5982 (a b c x y z : ℝ) : a = 2 * Real.cos x ∧ b = 2 * Real.cos y ∧ c = 2 * Real.cos z ↔ a = 2 * Real.cos x ∧ b = 2 * Real.cos y ∧ c = 2 * Real.cos z   :=  by sorry
