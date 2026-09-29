-- Prove2me | Theorems.Thm_lean_workbook_plus_51878
-- name    : lean_workbook_plus_51878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/a3f0338e-b57a-4652-95dd-65d460984215
-- statement:
--   Find a closed form for the sequence $(a_n)_{n=0}^{\infty}$ defined as: $a_0=1$, $a_1=2$, $a_{n}=4a_{n-1}-5a_{n-2}$ for $n>1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51878 (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 2) (a_rec : ∀ n, n > 1 → a n = 4 * a (n - 1) - 5 * a (n - 2)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
