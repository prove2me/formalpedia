-- Prove2me | solution 1 for PlusOneWilliams.lucasV_p_add_one_eq_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:24:13.118718+00:00
-- url     : https://prove2.me/submissions/6bb0f624-f0ac-4881-906d-897870516c24

-- Sol generated from Tropical/PlusOneWilliamsCore.lean
import Mathlib
import Definitions.Def_Tropical_PlusOneWilliamsCore
import Theorems.Thm_PlusOneWilliams_lucasV_eq_two_of_nonsquare_disc
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



/-! ## 2. The `p + 1` half of the discriminant gate -/




/-! ## 3. The `p - 1` half of the gate: a square discriminant degenerates -/



/-- **Exact value at the `p + 1` step for a square discriminant.** When `D` is
a square mod `p` the Frobenius fixes both roots, so `V_{p+1} = P² - 2` — the
value `2` is attained only in the degenerate case `D = 0`. -/
theorem lucasV_p_add_one_of_square_disc (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P t : ZMod p)
    (ht : t ^ 2 = P ^ 2 - 4) : lucasV P (p + 1) = P ^ 2 - 2 := by
  obtain ⟨a, b, hab, hsum⟩ := roots_of_disc_sqrt p hp2 P t ht
  rw [lucasV_eq_pow_add_pow hab hsum, pow_succ, pow_succ, ZMod.pow_card, ZMod.pow_card]
  have h : a * a + b * b = (a + b) ^ 2 - 2 * (a * b) := by ring
  rw [h, hab, hsum]; ring



/-! ## 4. The gcd step returns the factor -/


/-! ## 5. Smoothness feeds the exponent: `p + 1` powersmooth ⇒ `(p+1) ∣ M` -/




/-! ## 6. The degenerate base `P = 2` (`D = 0`) -/




/-! ## 7. Bases 3 and 7 share a square class -/




open PlusOneWilliams in
theorem solution(p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P : ZMod p) :
    lucasV P (p + 1) = 2 ↔ (¬ IsSquare (P ^ 2 - 4) ∨ P ^ 2 - 4 = 0) := by
  constructor
  · intro h
    by_cases hsq : IsSquare (P ^ 2 - 4)
    · right
      obtain ⟨r, hr⟩ := hsq
      have ht : r ^ 2 = P ^ 2 - 4 := by rw [hr]; ring
      have hval := lucasV_p_add_one_of_square_disc p hp2 P r ht
      rw [h] at hval
      linear_combination -hval
    · exact Or.inl hsq
  · rintro (h | h)
    · exact lucasV_eq_two_of_nonsquare_disc p hp2 P h dvd_rfl
    · have ht : (0 : ZMod p) ^ 2 = P ^ 2 - 4 := by rw [h]; ring
      rw [lucasV_p_add_one_of_square_disc p hp2 P 0 ht]
      linear_combination h
