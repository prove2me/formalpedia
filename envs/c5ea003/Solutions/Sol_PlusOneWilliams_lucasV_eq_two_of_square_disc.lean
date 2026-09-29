-- Prove2me | solution 1 for PlusOneWilliams.lucasV_eq_two_of_square_disc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:24:12.553984+00:00
-- url     : https://prove2.me/submissions/77070249-12a5-4c0b-b9e1-9f195d6f9985

-- Sol generated from Tropical/PlusOneWilliamsCore.lean
import Mathlib
import Definitions.Def_Tropical_PlusOneWilliamsCore
import Theorems.Thm_PlusOneWilliams_roots_of_disc_sqrt

/-!
# The Williams `p + 1` method: Lucas sequences and the discriminant gate

This file formalises the *arithmetic core* of the round-16 experiment
`PLUSONE-SMOOTH-NULL` (paper 64). The experiment measured, over 40 matched
semiprime pairs, that the classical Williams `p + 1` method (bases `P = 3, 5, 7`,
exponent `M = lcm(1..100)`) factors the `PLUSONE` class 24/40 and the `GENERAL`
class 0/40, and — the new structural finding — that the per-base success set is
*exactly* the set of instances with `(D | p) = -1`, where `D = P² - 4` is the
discriminant of the Lucas sequence.

Here we prove the theorems behind those numbers.

* `lucasV` — the Lucas `V`-sequence with parameters `(P, Q = 1)`, over any
  commutative ring; `lucasV_eq_pow_add_pow` is its Binet form.
* `lucasV_eq_two_of_nonsquare_disc` — **the `p + 1` half of the gate.** If
  `D = P² - 4` is a non-square mod the odd prime `p` and `(p + 1) ∣ M`, then
  `V_M ≡ 2 (mod p)`. The proof builds the quadratic extension
  `𝔽_p[X]/(X² - D) ≅ 𝔽_{p²}`, exhibits the two conjugate roots
  `a, b = (P ± √D)/2` of `x² - Px + 1`, and shows the Frobenius swaps them, so
  `a^{p+1} = ab = 1`.
* `lucasV_eq_two_of_square_disc` — **the `p - 1` half of the gate.** If `D` is a
  square mod `p` the roots are already in `𝔽_p`, so the relevant order divides
  `p - 1`, not `p + 1`: the method silently degenerates to Pollard `p - 1`.
  This is why the observed success rate equals the `(D | p) = -1` rate exactly.
* `williams_gcd_eq_factor` — the gcd step really returns the factor `p`.
* `lucasV_two_eq_two`, `plusOne_base_two_degenerate` — the base `P = 2` has
  `D = 0` and the sequence is constant `2`, so the gcd is always `N`: the
  degenerate base observed in the experiment.
* `legendreSym_fortyfive_eq_five`, `base_three_seven_same_gate` — `D₃ = 5` and
  `D₇ = 45 = 5 · 3²` lie in the same square class, so bases `3` and `7` succeed
  on *exactly* the same primes (observed: 11/40 for both, on the same instances).
-/

open PlusOneWilliams

open Polynomial

/-! ## 1. The Lucas `V`-sequence with `Q = 1` -/




lemma lucasV_succ_succ {R : Type*} [CommRing R] (P : R) (n : ℕ) :
    lucasV P (n + 2) = P * lucasV P (n + 1) - lucasV P n := rfl


/-- **Binet form.** If `a·b = 1` and `a + b = P` then `V_n = aⁿ + bⁿ`. -/
lemma lucasV_eq_pow_add_pow {R : Type*} [CommRing R] {P a b : R}
    (hab : a * b = 1) (hsum : a + b = P) (n : ℕ) :
    lucasV P n = a ^ n + b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => show (2 : R) = _; norm_num
  | one => show P = _; simp [← hsum]
  | more n ih1 ih2 =>
      rw [lucasV_succ_succ, ih1, ih2, ← hsum]
      have h : a ^ (n + 2) + b ^ (n + 2)
          = (a + b) * (a ^ (n + 1) + b ^ (n + 1)) - (a * b) * (a ^ n + b ^ n) := by ring
      rw [h, hab]; ring

/-- If both conjugate roots are killed by the exponent `M`, then `V_M = 2`. -/
lemma lucasV_eq_two_of_pow_eq_one {R : Type*} [CommRing R] {P a b : R}
    (hab : a * b = 1) (hsum : a + b = P) {M : ℕ} (ha : a ^ M = 1) (hb : b ^ M = 1) :
    lucasV P M = 2 := by
  rw [lucasV_eq_pow_add_pow hab hsum, ha, hb]; norm_num


/-! ## 2. The `p + 1` half of the discriminant gate -/




/-! ## 3. The `p - 1` half of the gate: a square discriminant degenerates -/






/-! ## 4. The gcd step returns the factor -/


/-! ## 5. Smoothness feeds the exponent: `p + 1` powersmooth ⇒ `(p+1) ∣ M` -/




/-! ## 6. The degenerate base `P = 2` (`D = 0`) -/




/-! ## 7. Bases 3 and 7 share a square class -/




open PlusOneWilliams in
theorem solution(p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P t : ZMod p)
    (ht : t ^ 2 = P ^ 2 - 4) {M : ℕ} (hM : (p - 1) ∣ M) :
    lucasV P M = 2 := by
  obtain ⟨a, b, hab, hsum⟩ := roots_of_disc_sqrt p hp2 P t ht
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hab
    exact zero_ne_one hab
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, mul_zero] at hab
    exact zero_ne_one hab
  obtain ⟨k, rfl⟩ := hM
  refine lucasV_eq_two_of_pow_eq_one hab hsum ?_ ?_
  · rw [pow_mul, ZMod.pow_card_sub_one_eq_one ha0, one_pow]
  · rw [pow_mul, ZMod.pow_card_sub_one_eq_one hb0, one_pow]
