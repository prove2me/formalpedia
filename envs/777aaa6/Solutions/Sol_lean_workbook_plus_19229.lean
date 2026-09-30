-- Prove2me | solution 1 for lean_workbook_plus_19229
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:00:12.465517+00:00
-- url     : https://prove2.me/submissions/8eda4a93-5ce2-4588-9c4b-02282f90f54f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem solution (n : ℕ) (h1 : Nat.gcd n 180 = 12)
    (h2 : Nat.lcm n 180 = 720) : n = 48 := by
  have he := Nat.gcd_mul_lcm n 180
  rw [h1, h2] at he
  omega

example : Nat.gcd 48 180 = 12 ∧ Nat.lcm 48 180 = 720 := by decide

#print axioms solution
