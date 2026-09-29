-- Prove2me | Theorems.Thm_lean_workbook_plus_23959
-- name    : lean_workbook_plus_23959
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d16f5b0f-388d-44bd-87c2-64385823016c
-- statement:
--   Find the sum of $2^3 + 3^3 + ... + 21^3$ minus the sum of $2+3+ ... +21$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23959 (n : ℕ) : (∑ k in Finset.Icc 2 21, k^3) - (∑ k in Finset.Icc 2 21, k) = 53130   :=  by sorry
