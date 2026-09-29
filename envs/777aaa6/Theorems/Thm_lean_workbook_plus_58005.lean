-- Prove2me | Theorems.Thm_lean_workbook_plus_58005
-- name    : lean_workbook_plus_58005
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0b13d459-9895-4c6f-a4f1-abec6a11f1f5
-- statement:
--   Given $s_j = 11k + r_j$ and $s_i = 11m + r_i$, how does subtracting these equations lead to $s_j - s_i = 11(k-m) + (r_j - r_i)$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58005 (k m : ℤ) (r₁ r₂ : ℕ) : 11 * k + r₁ - (11 * m + r₂) = 11 * (k - m) + (r₁ - r₂)   :=  by sorry
