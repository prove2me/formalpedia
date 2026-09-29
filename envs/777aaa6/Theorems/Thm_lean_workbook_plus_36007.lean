-- Prove2me | Theorems.Thm_lean_workbook_plus_36007
-- name    : lean_workbook_plus_36007
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6cf87aa4-3123-4d90-8ef2-7128f0dee965
-- statement:
--   Reformulated problem: Does there exist a positive integer $m$ such that for all $n\geq m,$ either $\sum_{i=1}^na_i\geq \prod_{i=1}^na_i$ or $\sum_{i=1}^na_i\leq \prod_{i=1}^na_i?$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36007  (a : ℕ → ℕ) (h1 : ∃ n, a n ≠ 0) :
  ∃ m, ∀ n ≥ m, (∑ i in Finset.range n, a i) ≥ (∏ i in Finset.range n, a i) ∨ (∑ i in Finset.range n, a i) ≤ (∏ i in Finset.range n, a i)   :=  by sorry
