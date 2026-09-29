-- Prove2me | Theorems.Thm_lean_workbook_plus_25527
-- name    : lean_workbook_plus_25527
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e9ce8d4e-8315-418c-8bb0-7777bbf2ae43
-- statement:
--   If $p>2$ is prime number and $m$ and $n$ are positive integers such that $\frac{m}{n}=1+\frac{1}{2}+\frac{1}{3}+...+\frac{1}{p-1}$, prove that $p$ divides $m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25527 : ∀ p : ℕ, p.Prime ∧ p > 2 → ∀ m n : ℕ, (m / n = ∑ i in Finset.Ico 1 (p-1), (1 / (i + 1))) → p ∣ m   :=  by sorry
