-- Prove2me | Theorems.Thm_lean_workbook_plus_75278
-- name    : lean_workbook_plus_75278
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/3029709d-f85f-4bc4-a0f1-2cc459ffe975
-- statement:
--   Let $p_1,p_2,..p_n$ be different primes with integer $n \ge 1$. Show that $n=1, p_1=3$ is the only solution for $\prod_{i=1}^{n}(1-\frac{1}{p_i}) = \frac{2}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75278 (n : ℕ) (p : ℕ → ℕ) (hp : ∀ i, Nat.Prime (p i)) (hpi : ∀ i j, i ≠ j → p i ≠ p j) (hprod : ∏ i in Finset.range n, (1 - 1 / p i) = 2 / 3) : n = 1 ∧ p 0 = 3   :=  by sorry
