-- Prove2me | Theorems.Thm_lean_workbook_plus_45013
-- name    : lean_workbook_plus_45013
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b4391d21-c02c-430d-859f-581785fd9b11
-- statement:
--   Prove that $2^1+2^2+2^3+\dots+2^x = 2^{x+1}-2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45013 : ∀ x : ℕ, ∑ i in Finset.range (x+1), 2^i = 2^(x+1) - 2   :=  by sorry
