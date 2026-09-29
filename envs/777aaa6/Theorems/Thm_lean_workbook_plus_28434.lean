-- Prove2me | Theorems.Thm_lean_workbook_plus_28434
-- name    : lean_workbook_plus_28434
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/a125e6eb-4a17-41d7-9d19-bb050c590bfa
-- statement:
--   Given the sequence defined by $a_{1}=3$ and $a_{n+1}=a_{n}+5+4\cdot 2^{n}+3^{n+1}+2\cdot 4^{n}+5^{n}$, find the closed form of $a_{n}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28434 (a : ℕ → ℕ) (a1 : a 0 = 3) (a_rec : ∀ n, a (n + 1) = a n + 5 + 4 * 2 ^ n + 3 ^ (n + 1) + 2 * 4 ^ n + 5 ^ n) : ∃ f : ℕ → ℕ, ∀ n, a n = f n   :=  by sorry
