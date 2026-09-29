-- Prove2me | Theorems.Thm_lean_workbook_plus_39039
-- name    : lean_workbook_plus_39039
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/694bb070-da21-4fee-a26c-ad29c177cfa7
-- statement:
--   If $k$ is odd, then prove that $\binom{k+3}{2}\cdot (-1)^{k+1}+\binom{k+2}{2}\cdot (-1)^{k} = k+2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39039 (k : ℕ) (h : k % 2 = 1) : (k + 3).choose 2 * (-1 : ℤ) ^ (k + 1) + (k + 2).choose 2 * (-1) ^ k = (k + 2)   :=  by sorry
