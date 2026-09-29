-- Prove2me | Theorems.Thm_lean_workbook_plus_6901
-- name    : lean_workbook_plus_6901
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e1fddd25-67dc-4753-acb4-cc58fe3c1940
-- statement:
--   Prove that $\sum_{i=m}^{m+k}|a_i|<\varepsilon$ for all $m\ge N$ and all $k\ge 0$ if $\sum |a_n|$ converges.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6901 (a : ℕ → ℝ) (N : ℕ) (hN : ∀ m ≥ N, ∀ k ≥ 0, ∑ i in Finset.range k, |a (m + i)| < ε) : ∀ m ≥ N, ∀ k ≥ 0, ∑ i in Finset.range k, |a (m + i)| < ε   :=  by sorry
