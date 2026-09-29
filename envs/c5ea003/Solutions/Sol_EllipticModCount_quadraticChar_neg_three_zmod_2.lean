-- Prove2me | solution 2 for EllipticModCount.quadraticChar_neg_three_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:37:03.478575+00:00
-- url     : https://prove2.me/submissions/00de49b5-eacf-4fda-94bc-13767618fd33

import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticVerticalMoment
theorem solution {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    quadraticChar (ZMod p) (-3) = -1 ↔ p % 3 = 2 := by
  have hpp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
  have hleg : quadraticChar (ZMod p) (-3) = legendreSym p (-3) := by
    simp [legendreSym]
  -- `(-3 / p) = (-1 / p) (3 / p) = (p / 3)` by quadratic reciprocity
  have hsplit : legendreSym p (-3) = legendreSym 3 p := by
    rw [show (-3 : ℤ) = -1 * ((3 : ℕ) : ℤ) by norm_num, legendreSym.mul,
      legendreSym.at_neg_one hp2, legendreSym.quadratic_reciprocity' (by norm_num : 3 ≠ 2) hp2, ZMod.χ₄_eq_neg_one_pow hodd]
    have h1 : (3 : ℕ) / 2 * (p / 2) = p / 2 := by omega
    rw [h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := by
      intro h
      have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp h3).symm
    omega
  rw [hleg, hsplit, legendreSym.mod 3 (p : ℤ), ← Int.natCast_mod]
  rcases hmod with h | h
  · rw [h]
    simp [legendreSym.at_one]
  · rw [h]
    have h2 : legendreSym 3 (2 : ℤ) = -1 := by
      rw [legendreSym.at_two (by norm_num : 3 ≠ 2)]
      decide
    simp [h2]
