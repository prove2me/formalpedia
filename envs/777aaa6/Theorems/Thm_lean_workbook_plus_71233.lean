-- Prove2me | Theorems.Thm_lean_workbook_plus_71233
-- name    : lean_workbook_plus_71233
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/22294df5-46af-4225-acb7-4ea83ee092ba
-- statement:
--   Prove that $\binom{n+1}{r+1} = \sum_{k=0}^{n}\binom{k}{r}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71233 (n r : ℕ) : ∑ k in Finset.range (n+1), choose k r = choose (n+1) (r+1)   :=  by sorry
