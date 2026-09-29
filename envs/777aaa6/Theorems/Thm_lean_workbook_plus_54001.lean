-- Prove2me | Theorems.Thm_lean_workbook_plus_54001
-- name    : lean_workbook_plus_54001
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/b5de2e82-f31e-4e1c-9544-322c071a11a1
-- statement:
--   Complete the square $px^2-qx = p \, (x-\frac{q}{2p})^2 - \frac{q^2}{4p}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54001 (p : ℝ) (q : ℝ) (h : p ≠ 0) : p * x ^ 2 - q * x = p * (x - q / (2 * p)) ^ 2 - q ^ 2 / (4 * p)   :=  by sorry
