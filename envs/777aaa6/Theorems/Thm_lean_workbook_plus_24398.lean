-- Prove2me | Theorems.Thm_lean_workbook_plus_24398
-- name    : lean_workbook_plus_24398
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4f5fbe1b-9a85-404a-8cad-5d83a5eac631
-- statement:
--   Evaluate the sum: $\sum\limits_{k=2}^{5} {k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24398 (f : ℕ → ℕ) : ∑ k in Finset.Icc 2 5, k = 14   :=  by sorry
