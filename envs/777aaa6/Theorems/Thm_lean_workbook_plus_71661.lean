-- Prove2me | Theorems.Thm_lean_workbook_plus_71661
-- name    : lean_workbook_plus_71661
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/00e253a5-4f51-48a3-9783-54f199d68bc2
-- statement:
--   Prove that there are exist: $\epsilon_i\in \{1;-1\}$ so that the following inequality is true for all real $x_i$ ( $\forall i=\overline{1;n}$ ): $(\sum_{i=1}^n x_i)^2+(\sum_{i=1}^n \epsilon_i x_i)^2\leq \sum_{i=1}^n x_i^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71661 (n:ℕ) (x:ℕ → ℝ): ∃ e:ℕ → ℝ, ∀ i ∈ Finset.range n, e i = 1 ∨ e i = -1 ∧ (∑ i in Finset.range n, x i)^2 + (∑ i in Finset.range n, e i * x i)^2 ≤ ∑ i in Finset.range n, (x i)^2   :=  by sorry
