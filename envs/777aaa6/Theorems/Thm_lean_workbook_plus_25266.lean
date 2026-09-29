-- Prove2me | Theorems.Thm_lean_workbook_plus_25266
-- name    : lean_workbook_plus_25266
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d2269290-9911-4323-a24c-8d6dc31cd63e
-- statement:
--   Prove that for all integers $n$ , \n\n $\left(1+\dfrac{1}{1^3}\right)\left(1+\dfrac{1}{2^3}\right)\left(1+\dfrac{1}{3^3}\right)...\left(1+\dfrac{1}{n^3}\right) < 3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25266 : ∀ n : ℕ, (∏ k in Finset.Icc 1 n, (1 + 1 / k ^ 3)) < 3   :=  by sorry
