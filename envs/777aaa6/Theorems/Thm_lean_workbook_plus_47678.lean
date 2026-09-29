-- Prove2me | Theorems.Thm_lean_workbook_plus_47678
-- name    : lean_workbook_plus_47678
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d3a4b954-1686-49e8-a279-08dc20a62844
-- statement:
--   Use the properties of summation: $\sum ka_n = k \sum a_n$ and $\sum \left(a_n + b_n\right)= \sum a_n + \sum b_n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47678 (f : ℕ → ℝ) (k : ℝ) (n : ℕ) : ∑ i in Finset.range n, k * f i = k * ∑ i in Finset.range n, f i   :=  by sorry
