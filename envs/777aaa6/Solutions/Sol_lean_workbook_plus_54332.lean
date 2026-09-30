-- Prove2me | solution 1 for lean_workbook_plus_54332
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:33.701219+00:00
-- url     : https://prove2.me/submissions/8afbce18-a95e-4583-b590-ab443e7b2f8e

import Mathlib.Data.Int.GCD

set_option autoImplicit false

theorem solution (a₁ a₂ : ℕ) :
    ∃ x y : ℤ, x * a₁ + y * a₂ = Nat.gcd a₁ a₂ := by
  refine ⟨Nat.gcdA a₁ a₂, Nat.gcdB a₁ a₂, ?_⟩
  simpa only [mul_comm] using (Nat.gcd_eq_gcd_ab a₁ a₂).symm

#print axioms solution
