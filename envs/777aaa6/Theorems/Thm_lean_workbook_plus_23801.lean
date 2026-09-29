-- Prove2me | Theorems.Thm_lean_workbook_plus_23801
-- name    : lean_workbook_plus_23801
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d1422de2-f93a-45bd-b852-20dbef3a2006
-- statement:
--   Let $a_0=1,a_1=3$ and for $n\geq1$ we have $a_{n+2}=2a_{n+1}+2a_n-3$ .Find formula for every $a_i$ of this sequence.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23801 (n : ℕ) (a : ℕ → ℕ) (a0 : a 0 = 1) (a1 : a 1 = 3) (a_rec : ∀ n ≥ 1, a (n + 2) = 2 * a (n + 1) + 2 * a n - 3) : ∃ f : ℕ → ℕ, ∀ n, a n = f n   :=  by sorry
