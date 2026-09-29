-- Prove2me | Theorems.Thm_lean_workbook_plus_56436
-- name    : lean_workbook_plus_56436
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d06bb22e-398d-4b6b-849a-f4e82483323a
-- statement:
--   What is $\sum_{x=1155}^{1155}x$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56436 (x : ℕ) : ∑ k in Finset.Icc 1155 1155, k = 1155   :=  by sorry
