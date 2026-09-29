-- Prove2me | Theorems.Thm_lean_workbook_plus_8672
-- name    : lean_workbook_plus_8672
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e74e0dd9-e002-4c18-b6ce-ebbf5fbc76a8
-- statement:
--   Derive the partial summation formula: $\sum_{n = 1}^Na_nb_n = a_{N + 1}B_N - \sum_{n = 1}^NB_N(a_{n + 1} - a_n)$, where $B_n = \sum_{k = 1}^nb_k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8672 (f g : ℕ → ℝ) (N : ℕ) : ∑ n in Finset.Icc 1 N, f n * g n
  = f (N + 1) * (∑ n in Finset.Icc 1 N, g n) -
    ∑ n in Finset.Icc 1 N, ((∑ k in Finset.Icc 1 n, g k) * (f (n + 1) - f n))   :=  by sorry
