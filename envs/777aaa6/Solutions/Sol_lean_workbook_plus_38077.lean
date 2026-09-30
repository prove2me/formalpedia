-- Prove2me | solution 1 for lean_workbook_plus_38077
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:09:51.704082+00:00
-- url     : https://prove2.me/submissions/66fe56bf-370f-4d18-8dfb-75715a320841

import Mathlib

set_option autoImplicit false

theorem coin_classification (p n d : ℕ) :
    (p + n + d = 21 ∧ p + 5 * n + 10 * d = 100 ∧
      0 < p ∧ 0 < n ∧ 0 < d) ↔
      (p, n, d) = (10, 4, 7) ∨ (p, n, d) = (5, 13, 3) := by
  simp only [Prod.mk.injEq]
  omega

theorem solution (p n d : ℕ) (h0 : p + n + d = 21)
    (h1 : p + 5 * n + 10 * d = 100) (h2 : 0 < p ∧ 0 < n ∧ 0 < d) :
    (p, n, d) = (10, 4, 7) ∨ (p, n, d) = (5, 13, 3) :=
  (coin_classification p n d).mp ⟨h0, h1, h2⟩

#print axioms solution
