-- Prove2me | Theorems.Thm_lean_workbook_plus_41515
-- name    : lean_workbook_plus_41515
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3a4f9b96-6bb9-4081-a38f-cd69cd3f923b
-- statement:
--   Prove that the sum of the first n odd numbers is $n^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41515 (n : ℕ) : ∑ i in Finset.range n, (2 * i + 1) = n^2   :=  by sorry
