-- Prove2me | Theorems.Thm_lean_workbook_plus_77624
-- name    : lean_workbook_plus_77624
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/45c46039-38c1-4e38-b7b1-9fadc475c883
-- statement:
--   Let $n \geq 1$ be a positive integer, and let $\mathcal{S} \subset {0, 1, 2, \ldots, n}$ such that $|\mathcal{S}| \geq \frac{n}{2}+1$. Show that some power of $2$ is either an element of $\mathcal{S}$ or the sum of two distinct elements of $\mathcal{S}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77624 (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ) (hS : (n : ℕ) / 2 + 1 ≤ S.card) : ∃ k : ℕ, (2 ^ k ∈ S) ∨ (∃ x y : ℕ, x ≠ y ∧ 2 ^ k = x + y)   :=  by sorry
