-- Prove2me | Theorems.Thm_lean_workbook_plus_79140
-- name    : lean_workbook_plus_79140
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ecdcb628-0e81-41dc-bb97-1c42b415e59b
-- statement:
--   Prove that for every positive integer $n$ an inequality $\dfrac1{3!}+\dfrac3{4!}+\ldots+\dfrac{2n-1}{(n+2)!}<\frac12$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79140 : ∀ n : ℕ, (∑ k in Finset.range n, ((2 * k - 1) / (k + 2)!)) < 1 / 2   :=  by sorry
