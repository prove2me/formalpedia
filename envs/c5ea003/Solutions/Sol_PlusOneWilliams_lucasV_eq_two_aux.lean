-- Prove2me | solution 1 for PlusOneWilliams.lucasV_eq_two_aux
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:17:34.058431+00:00
-- url     : https://prove2.me/submissions/d5db3ac6-f171-4111-adfd-8422a22ac826

-- Sol generated from Tropical/PlusOneWilliamsCore.lean
import Mathlib
import Definitions.Def_Tropical_PlusOneWilliamsCore

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

/-- The Lucas sequence commutes with ring homomorphisms (reduction mod `p`). -/
lemma map_lucasV {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : R) (n : ℕ) :
    f (lucasV P n) = lucasV (f P) n := by
  induction n using Nat.twoStepInduction with
  | zero => exact map_ofNat f 2
  | one => rfl
  | more n ih1 ih2 => simp [lucasV_succ_succ, ih1, ih2]

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
theorem solution{p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type*} [CommRing K]
    [CharP K p] (f : ZMod p →+* K) (hinj : Function.Injective f) (P : ZMod p) (s : K)
    (hs2 : s ^ 2 = f (P ^ 2 - 4)) (hsp : s ^ p = -s) {M : ℕ} (hM : (p + 1) ∣ M) :
    lucasV P M = 2 := by
  have hp' : p.Prime := Fact.out
  have hodd : Odd p := hp'.odd_of_ne_two hp2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp h)
    simpa using h2
  set c : K := f ((2 : ZMod p)⁻¹) with hc
  have hc2 : f 2 * c = 1 := by rw [hc, ← map_mul, mul_inv_cancel₀ h2ne, map_one]
  set a : K := (f P + s) * c with ha
  set b : K := (f P + -s) * c with hb
  have hsum : a + b = f P := by
    have h : a + b = f 2 * c * f P := by rw [ha, hb, map_ofNat]; ring
    rw [h, hc2, one_mul]
  have hab : a * b = 1 := by
    have h4 : f 4 = f 2 * f 2 := by rw [← map_mul]; norm_num
    have hfd : f (P ^ 2 - 4) = f P * f P - f 4 := by rw [map_sub, map_pow]; ring
    have h1 : a * b = (f P * f P - s ^ 2) * (c * c) := by rw [ha, hb]; ring
    rw [h1, hs2, hfd, h4]
    calc (f P * f P - (f P * f P - f 2 * f 2)) * (c * c) = (f 2 * c) * (f 2 * c) := by ring
      _ = 1 := by rw [hc2]; ring
  have hfP : (f P) ^ p = f P := by rw [← map_pow, ZMod.pow_card]
  have hcp : c ^ p = c := by rw [hc, ← map_pow, ZMod.pow_card]
  have hap : a ^ p = b := by
    rw [ha, mul_pow, add_pow_char _ _ p, hfP, hsp, hcp, hb]
  have hbp : b ^ p = a := by
    rw [hb, mul_pow, add_pow_char _ _ p, hfP, hodd.neg_pow, hsp, hcp, ha, neg_neg]
  have hapow : a ^ (p + 1) = 1 := by rw [pow_succ, hap, ← hab]; ring
  have hbpow : b ^ (p + 1) = 1 := by rw [pow_succ, hbp, ← hab]
  obtain ⟨k, rfl⟩ := hM
  have hA : a ^ ((p + 1) * k) = 1 := by rw [pow_mul, hapow, one_pow]
  have hB : b ^ ((p + 1) * k) = 1 := by rw [pow_mul, hbpow, one_pow]
  have key : f (lucasV P ((p + 1) * k)) = f 2 := by
    rw [map_lucasV, lucasV_eq_two_of_pow_eq_one hab hsum hA hB, map_ofNat]
  exact hinj key
