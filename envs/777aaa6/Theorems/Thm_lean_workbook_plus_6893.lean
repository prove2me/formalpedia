-- Prove2me | Theorems.Thm_lean_workbook_plus_6893
-- name    : lean_workbook_plus_6893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e6df1cce-ecb5-4735-b8ff-86f5d42f8097
-- statement:
--   Prove that for any integer $k$, $a = 3k-1$ and $b = 4-11k$ satisfy $22a + 6b = 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6893 : ∀ k : ℤ, 22 * (3 * k - 1) + 6 * (4 - 11 * k) = 2   :=  by sorry
