-- Prove2me | Theorems.Thm_lean_workbook_plus_7602
-- name    : lean_workbook_plus_7602
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f697a47e-e69d-4476-8227-73746dcf96d3
-- statement:
--   Prove $\sum_{j = 0}^n \dbinom{n}{j} = 2^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7602 (n : ℕ) : ∑ j in Finset.range (n + 1), choose n j = 2 ^ n   :=  by sorry
