-- Prove2me | Theorems.Thm_lean_workbook_plus_31672
-- name    : lean_workbook_plus_31672
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/2ab1997c-d9c6-4fe2-8c74-8416effade22
-- statement:
--   Derive $\frac{n+1}{2}\geq\sqrt[n]{n!}$ from $\sum_{k=1}^{n}k=\frac{n\left(n+1\right)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31672 : ∀ n : ℕ, (∑ k in Finset.Icc 1 n, k) = n * (n + 1) / 2 → (n + 1) / 2 ≥ (n! : ℝ) ^ (1 / n)   :=  by sorry
