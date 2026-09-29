-- Prove2me | Theorems.Thm_lean_workbook_plus_19348
-- name    : lean_workbook_plus_19348
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/692466db-6092-4133-9e6c-82f5c3482f95
-- statement:
--   $\frac{1}{27}(\frac{9-p}{2})^{2}\leq\frac{1}{p}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19348 : ∀ p : ℝ, p > 0 ∧ p ≠ 1 → 1 / 27 * ((9 - p) / 2) ^ 2 ≤ 1 / p   :=  by sorry
