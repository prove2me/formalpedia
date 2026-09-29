-- Prove2me | Theorems.Thm_lean_workbook_plus_1376
-- name    : lean_workbook_plus_1376
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/398efc3b-c599-4e2b-892a-116ab684cc1e
-- statement:
--   Prove that $2^{n-1}\left(1+\prod_{i=1}^n a_i\right)-\prod_{i=1}^n (1+a_i) \ge 0$ for $a_i \ge 1$ and $i = 1, 2, ..., n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1376 (n : ℕ) (a : ℕ → ℕ) (h : ∀ i, 1 ≤ a i) : 2 ^ (n - 1) * (1 + ∏ i in Finset.range n, a i) - ∏ i in Finset.range n, (1 + a i) ≥ 0   :=  by sorry
