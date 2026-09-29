-- Prove2me | Theorems.Thm_lean_workbook_plus_5799
-- name    : lean_workbook_plus_5799
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/fd5b449d-9f7c-4fad-ab56-f8829b6dd954
-- statement:
--   Let $F_0 = 0, F_{1} = 1$ , and for $n \ge 1, F_{n+1} = F_n + F_{n-1}$ . Define $a_n = \left(\frac{1 + \sqrt{5}}{2}\right)^n \cdot F_n$ . Then there are rational numbers $A$ and $B$ such that $\frac{a_{30} + a_{29}}{a_{26} + a_{25}} = A + B \sqrt{5}$ . Find $A + B$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5799 (a : ℕ → ℚ) (a0 : a 0 = 0) (a1 : a 1 = 1) (a_rec : ∀ n, n ≥ 1 → a (n + 1) = a n + a (n - 1)) : ∃ A B : ℚ, (a 30 + a 29) / (a 26 + a 25) = A + B * Real.sqrt 5 ∧ A + B = 1346269 / 196418   :=  by sorry
