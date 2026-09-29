-- Prove2me | Theorems.Thm_lean_workbook_plus_6357
-- name    : lean_workbook_plus_6357
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/003b64f1-60da-4c59-b6ad-f6248ffe164b
-- statement:
--   Prove that there exist infinitely many positive integers $n$ such that the number $\frac{1^2+2^2+\cdots+n^2}{n}$ is a perfect square. Obviously, $1$ is the least integer having this property. Find the next two least integers having this property.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6357 : ∃ n : ℕ, n > 1 ∧ ∃ k : ℕ, (∑ i in Finset.range n, i ^ 2) / n = k ^ 2   :=  by sorry
