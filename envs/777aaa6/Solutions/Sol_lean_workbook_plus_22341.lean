-- Prove2me | solution 1 for lean_workbook_plus_22341
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:13:43.866223+00:00
-- url     : https://prove2.me/submissions/2eeff057-f09f-4825-8ace-213e4feed696

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (h₀ : ∃ k, ∀ n, f n = k * n)
    (h₁ : ∀ x y, f (x ^ 2 - y ^ 2) = f x * f (2 * y)) :
    ∀ n, f n = 0 ∨ ∀ n, f n = n := by
  obtain ⟨k, hk⟩ := h₀
  have he := h₁ 1 0
  simp only [hk] at he
  norm_num at he
  intro n
  left
  simp [hk, he]

#print axioms solution
