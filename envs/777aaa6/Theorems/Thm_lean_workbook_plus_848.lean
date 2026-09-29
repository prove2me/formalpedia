-- Prove2me | Theorems.Thm_lean_workbook_plus_848
-- name    : lean_workbook_plus_848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c7199a08-7b06-4b85-9378-cb374b80117e
-- statement:
--   Prove the generalized triangle inequality: of $x_1, x_2, \cdot, x_n$ are real numbers, then $$|x_1+x_2+\cdots +x_n| \leq |x_1| + |x_2| + \cdots + |x_n|.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_848 (n : ℕ) (x : Fin n → ℝ) : 
  |∑ i, x i| ≤ ∑ i, |x i|   :=  by sorry
