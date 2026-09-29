-- Prove2me | Theorems.Thm_lean_workbook_plus_76064
-- name    : lean_workbook_plus_76064
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/f32579db-a120-4d76-a4e0-4504320e3533
-- statement:
--   A sequence $\{a_n\}^\infty_{n=0}$ of positive integers satisfy $a_0=0$, $a_1=2$, and $a_n+a_{n-2}=2(a_{n-1}+1)$ for all integers $n\ge2$. Find a closed-form formula for $a_n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76064 (a : ℕ → ℕ) (a0 : a 0 = 0) (a1 : a 1 = 2) (a_rec : ∀ n, n ≥ 2 → a n + a (n - 2) = 2 * (a (n - 1) + 1)) : ∃ f : ℕ → ℕ, ∀ n, a n = f n   :=  by sorry
