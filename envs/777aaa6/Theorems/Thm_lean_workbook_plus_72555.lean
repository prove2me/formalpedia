-- Prove2me | Theorems.Thm_lean_workbook_plus_72555
-- name    : lean_workbook_plus_72555
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/dd8e5ca8-9904-4d01-99c8-8c98a21300fd
-- statement:
--   Prove that $B_{n} \le 2n^{2}$ for all $n\in\mathbb{N}$ where $B_{n}=n^{2}A_{n}=\sum_{k=1}^{n} \left(k+\frac{1}{k} \right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72555 : ∀ n : ℕ, (n : ℝ)^2 * (∑ k in Finset.Icc 1 n, (k + 1/k)) ≤ 2 * n^2   :=  by sorry
