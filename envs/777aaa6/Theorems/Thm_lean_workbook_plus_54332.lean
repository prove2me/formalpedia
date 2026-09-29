-- Prove2me | Theorems.Thm_lean_workbook_plus_54332
-- name    : lean_workbook_plus_54332
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/4748476e-e599-4ba8-91f7-e90d4033549b
-- statement:
--   Use Bezout's lemma to find $x$ and $y$ such that $x a_1 + y a_2 = \gcd(a_1, a_2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54332 (a₁ a₂ : ℕ) : ∃ x y : ℤ, x * a₁ + y * a₂ = Nat.gcd a₁ a₂   :=  by sorry
