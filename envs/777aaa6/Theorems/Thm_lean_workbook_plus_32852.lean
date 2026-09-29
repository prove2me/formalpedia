-- Prove2me | Theorems.Thm_lean_workbook_plus_32852
-- name    : lean_workbook_plus_32852
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1a251263-9f0e-459f-ba77-7dac62e73019
-- statement:
--   Find the convergence of the series $\sum\frac1{k^{4}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32852 : ∀ N : ℕ, ∃ M : ℝ, ∀ n : ℕ, n ≥ N → M ≤ ∑ i in Finset.range n, (1 : ℝ) / i ^ 4   :=  by sorry
