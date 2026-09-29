-- Prove2me | Theorems.Thm_lean_workbook_plus_27270
-- name    : lean_workbook_plus_27270
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/e8a6f04c-f757-4a4c-bf37-ad995cda2be7
-- statement:
--   Show that $A_n=\prod_{j=0}^{n-1}\cfrac{(3j+1)!}{(n+j)!}$ is an integer, for any positive integer $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27270 (n : ℕ) : ∃ k : ℕ, (k : ℚ) = ∏ j in Finset.range n, ((3 * j + 1)! / (n + j)!)   :=  by sorry
