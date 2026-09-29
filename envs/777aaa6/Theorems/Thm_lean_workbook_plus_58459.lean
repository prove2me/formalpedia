-- Prove2me | Theorems.Thm_lean_workbook_plus_58459
-- name    : lean_workbook_plus_58459
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3f16818c-0466-4706-987f-38d0f4a3479e
-- statement:
--   Prove that the number $q_{n} = (10^{3n}+3 \times 10^{2n}-4)/9$ is irrational for all integers n > 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58459 (n : ℕ) (hn : 1 < n) : ¬ ∃ q : ℚ, (q : ℝ) = (10^(3*n) + 3 * 10^(2*n) - 4) / 9   :=  by sorry
