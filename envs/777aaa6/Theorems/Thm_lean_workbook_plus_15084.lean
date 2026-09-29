-- Prove2me | Theorems.Thm_lean_workbook_plus_15084
-- name    : lean_workbook_plus_15084
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/408d7e30-c841-46f2-8c22-bb02c343e511
-- statement:
--   Let $\mathbb Z^+$ denote the set of all nonnegative integers. Define a recurrent sequence $\left(a_n\right)_{n\in\mathbb{Z}^+}$ by $a_0=a_1=1$ and the recurrence equation $a_{n+1}a_{n-1}=a_n\left(a_n+1\right)$ for every positive integer n. Prove that $a_n$ is an integer for every $n\in\mathbb{Z}^+$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15084 {a : ℕ → ℚ} (a0 : a 0 = 1) (a1 : a 1 = 1) (a_rec : ∀ n, a (n + 1) * a (n - 1) = a n * (a n + 1)) : ∀ n, a n = ⌊a n⌋   :=  by sorry
