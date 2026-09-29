-- Prove2me | Theorems.Thm_lean_workbook_plus_50196
-- name    : lean_workbook_plus_50196
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/22cfe2b3-cbb8-4455-b2c1-0a65b7397cb7
-- statement:
--   Prove that $\frac 12 \left(1-\frac{1}{n+2}\right)\leq \sum_{k=1}^n \frac{k}{n^2+n+k}<\frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50196 (n : ℕ) : 1 / 2 * (1 - 1 / (n + 2)) ≤ ∑ k in Finset.Icc 1 n, k / (n ^ 2 + n + k) ∧ ∑ k in Finset.Icc 1 n, k / (n ^ 2 + n + k) < 1 / 2   :=  by sorry
