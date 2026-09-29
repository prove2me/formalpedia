-- Prove2me | Theorems.Thm_lean_workbook_plus_75350
-- name    : lean_workbook_plus_75350
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/2db7c2ee-e12b-4139-b644-75e8871f0e77
-- statement:
--   Prove: If an integer $n$ is a sum of two square, then $2n$ is also a sum of two squares.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75350 (n : ℤ) : ∃ a b : ℤ, a^2 + b^2 = n → ∃ c d : ℤ, c^2 + d^2 = 2*n   :=  by sorry
