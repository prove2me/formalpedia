-- Prove2me | Theorems.Thm_lean_workbook_plus_24194
-- name    : lean_workbook_plus_24194
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/11993288-531f-44ce-890d-161b216cd507
-- statement:
--   Let $ n$ be positive integer. Prove the following inequality: \n\n$ e<(\frac{(n+1)^{2n+1}}{(n!)^{2}})^{\frac{1}{2n}}<e^{1+\frac{1}{12(n+1)}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24194 (n : ℕ) (hn : 0 < n) : e < ((n + 1) ^ (2 * n + 1) / (n!) ^ 2) ^ (1 / (2 * n)) ∧ ((n + 1) ^ (2 * n + 1) / (n!) ^ 2) ^ (1 / (2 * n)) < e ^ (1 + 1 / (12 * (n + 1)))   :=  by sorry
