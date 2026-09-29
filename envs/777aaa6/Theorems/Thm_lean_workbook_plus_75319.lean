-- Prove2me | Theorems.Thm_lean_workbook_plus_75319
-- name    : lean_workbook_plus_75319
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c5a4dac2-e971-411c-b27a-3c4e92a4f285
-- statement:
--   Determine with proof, if there exists a sequence $(a_n)_{n \geq 1}$ of positive numbers such that both inequalities (i) and (ii) hold for any positive integer $n$ .\n\n(i) $\sum\limits_{i = 1}^{n}a_i \leq n^2$\n(ii) $\sum\limits_{i = 1}^{n}\frac{1}{a_i} \leq 2018$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75319 (n : ℕ) (hn : 0 < n) : ∃ a : ℕ → ℝ, (∑ i in Finset.range n, a i ≤ n^2 ∧ ∑ i in Finset.range n, (1 / a i) ≤ 2018)   :=  by sorry
