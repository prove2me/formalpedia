-- Prove2me | Theorems.Thm_lean_workbook_plus_32759
-- name    : lean_workbook_plus_32759
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f13d1d2a-6899-49fc-af6a-eccc248ee7b7
-- statement:
--   Let $a_1=1$ and $a_{n+1}=1+a_1\cdot a_2 \cdot ... \cdot a_n$. Prove that $\sum_{n=1}^{\infty} \frac{1}{a_n}=2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32759 (a : ℕ → ℕ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = 1 + (∏ i in Finset.range (n + 1), a i)) : ∑' i : ℕ, (1 / a i) = 2   :=  by sorry
