-- Prove2me | Theorems.Thm_lean_workbook_plus_6120
-- name    : lean_workbook_plus_6120
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3d317510-b4a8-4d10-905c-349450fb1b71
-- statement:
--   Prove that $\sum_{k=0}^n\binom nk x^k=(x+1)^n.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6120 (n : ℕ) : ∑ k in Finset.range (n+1), (n.choose k) * x ^ k = (x + 1) ^ n   :=  by sorry
