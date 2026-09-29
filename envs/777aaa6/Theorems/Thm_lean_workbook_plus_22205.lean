-- Prove2me | Theorems.Thm_lean_workbook_plus_22205
-- name    : lean_workbook_plus_22205
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/469e1c91-ddb6-4299-ba3d-e9f08db7f82e
-- statement:
--   Find all function $f: \mathbb{N} \to \mathbb{N}$ such that $f(0)=1$ and $f(n)=2f\left(\left \lfloor{\dfrac{n}{5}} \right \rfloor \right) + 3f\left(\left \lfloor{\dfrac{n}{25}} \right \rfloor \right),\,\forall n\in \mathbb{N^*}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22205 (f : ℕ → ℕ) (h₁ : f 0 = 1) (h₂ : ∀ n ∈ Set.Ioi 0, f n = 2 * f (Nat.floor (n / 5)) + 3 * f (Nat.floor (n / 25))) : ∀ n ∈ Set.Ioi 0, f n = 5 ^ (Nat.floor (Real.logb 5 n))   :=  by sorry
