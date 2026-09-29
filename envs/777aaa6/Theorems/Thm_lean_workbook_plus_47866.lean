-- Prove2me | Theorems.Thm_lean_workbook_plus_47866
-- name    : lean_workbook_plus_47866
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3e7fa6e8-e937-450b-a43f-e6f9ae5a800c
-- statement:
--   $\frac{x}{x^2+y^2}\leq \frac{1}{2y}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47866 : ∀ x y : ℝ, (x ≠ 0 ∧ y ≠ 0) → x / (x ^ 2 + y ^ 2) ≤ 1 / (2 * y)   :=  by sorry
