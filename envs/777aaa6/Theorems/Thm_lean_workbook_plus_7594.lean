-- Prove2me | Theorems.Thm_lean_workbook_plus_7594
-- name    : lean_workbook_plus_7594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c63c23aa-8c55-4319-af82-97efd362ec3a
-- statement:
--   Let $ p(x) = x^2+ax+b $ be a quadratic polynomial with $ a,b\in\mathbb{Z} $ .Given any integer $n$ ,Show that there is an integer $M$ such that $ p(n) p(n+1) = p(M) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7594 (p : ℤ → ℤ) (a b n : ℤ) (hp : ∀ x : ℤ, p x = x^2 + a * x + b) : ∃ M : ℤ, p n * p (n + 1) = p M   :=  by sorry
