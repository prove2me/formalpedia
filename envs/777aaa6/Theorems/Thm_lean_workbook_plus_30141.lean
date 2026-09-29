-- Prove2me | Theorems.Thm_lean_workbook_plus_30141
-- name    : lean_workbook_plus_30141
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c4774589-8f9c-4fdf-ab58-c84ecc68f433
-- statement:
--   Prove that the series $\frac{1}{2} + \frac{1}{4} + \frac18 + ...$ is convergent
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30141 : ∀ x : ℝ, 0 < x ∧ x < 1 → ∃ y, ∑' i : ℕ, (1/2)^i = y   :=  by sorry
