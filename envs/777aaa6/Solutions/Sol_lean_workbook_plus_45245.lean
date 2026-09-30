-- Prove2me | solution 1 for lean_workbook_plus_45245
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:50:17.611214+00:00
-- url     : https://prove2.me/submissions/62376bbe-ae30-4fb2-bd4c-a2b81e32135a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b : ℤ) (h : Nat.gcd a.natAbs b.natAbs = 1) :
    ∃ x y : ℤ, a * x + b * y = 1 := by
  refine ⟨a.gcdA b, a.gcdB b, ?_⟩
  rw [← Int.gcd_eq_gcd_ab]
  exact_mod_cast h

#print axioms solution
