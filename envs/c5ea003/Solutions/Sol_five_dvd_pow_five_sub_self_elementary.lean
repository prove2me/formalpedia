-- Prove2me | solution 1 for five_dvd_pow_five_sub_self_elementary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:53:34.547947+00:00
-- url     : https://prove2.me/submissions/c8b0ef4a-929a-40c4-8a06-f710c3b0a75f

-- Sol generated from Probability/FermatLittleFive.lean
import Mathlib

/-!
# Fermat's Little Theorem and the divisibility `5 ∣ a ^ 5 - a`

This file records Fermat's little theorem over the integers together with several
proofs of the special case `5 ∣ a ^ 5 - a`.
-/

open scoped BigOperators





theorem solution(a : ℤ) : 5 ∣ a ^ 5 - a := by
  have hfact : a ^ 5 - a = (a - 1) * a * (a + 1) * (a ^ 2 + 1) := by ring
  rw [hfact]
  have h5 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  rcases h5 with h | h | h | h | h
  · -- 5 ∣ a
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by omega) _) _) _
  · -- 5 ∣ a - 1
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by omega) _) _) _
  · -- 5 ∣ a ^ 2 + 1
    have h2 : (5 : ℤ) ∣ a ^ 2 + 1 := by
      have : (a ^ 2 + 1) % 5 = 0 := by rw [pow_two, Int.add_emod, Int.mul_emod, h]; decide
      omega
    exact dvd_mul_of_dvd_right h2 _
  · -- 5 ∣ a ^ 2 + 1
    have h2 : (5 : ℤ) ∣ a ^ 2 + 1 := by
      have : (a ^ 2 + 1) % 5 = 0 := by rw [pow_two, Int.add_emod, Int.mul_emod, h]; decide
      omega
    exact dvd_mul_of_dvd_right h2 _
  · -- 5 ∣ a + 1
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by omega) _) _
