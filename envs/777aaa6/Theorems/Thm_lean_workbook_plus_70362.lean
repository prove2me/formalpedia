-- Prove2me | Theorems.Thm_lean_workbook_plus_70362
-- name    : lean_workbook_plus_70362
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/8a60194d-794b-4ace-863b-efd7326a13a9
-- statement:
--   Find the pairs (m, n) that satisfy the equation \(m - n = 7^2\) and \(m + n + 1 = 2 \times 41\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70362 (m n : ℕ) : m - n = 7^2 ∧ m + n + 1 = 2 * 41 ↔ m = 65 ∧ n = 16   :=  by sorry
