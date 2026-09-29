-- Prove2me | solution 1 for FactoringBarriers.nontrivialDivisor_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:36:16.850838+00:00
-- url     : https://prove2.me/submissions/5bc1b479-288b-4d53-a770-f1aef59417e0

-- Sol generated from Cryptography/FactoringBarriers/CongruenceOfSquares.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares

/-!
# The Structural Core: Congruences of Squares and Order Finding

Every general-purpose classical factoring algorithm that is not pure trial
division (CFRAC, quadratic sieve, number field sieve, Dixon's random squares,
and the classical post-processing of Shor's algorithm) reduces to the *same*
structural step:

  find `x, y` with `x² ≡ y² (mod N)` but `x ≢ ± y (mod N)`; then `gcd(x-y, N)`
  is a nontrivial factor of `N`.

This file proves that step rigorously, derives the order-finding reduction that
underlies Shor's algorithm from it, and shows that for a semiprime any
nontrivial divisor *is* one of the two prime factors, i.e. the structural step
completely solves the problem.

This is the "barrier 5" core: the reduction is unconditional, so the difficulty
of factoring is entirely concentrated in *producing* the congruence of squares
(equivalently, the multiplicative order), never in exploiting it.
-/

open FactoringBarriers



/-! ## The congruence-of-squares reduction -/



/-! ## For semiprimes the structural step is everything -/



/-! ## Sharpness: both exceptional congruences are genuinely needed -/



open FactoringBarriers in
theorem solution{p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : NontrivialDivisor (p * q) d) : d = p ∨ d = q := by
  obtain ⟨hdvd, hd1, hdlt⟩ := h
  by_cases hpd : p ∣ d
  · left
    obtain ⟨k, hk⟩ := hpd
    have hkq : k ∣ q := by
      have : p * k ∣ p * q := by rw [← hk]; exact hdvd
      exact (mul_dvd_mul_iff_left hp.pos.ne').mp this
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq k hkq) with hk1 | hkq'
    · rw [hk, hk1, mul_one]
    · exfalso
      rw [hk, hkq'] at hdlt
      omega
  · right
    have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
    have hdq : d ∣ q := (Nat.Coprime.dvd_of_dvd_mul_left (hcop.symm) hdvd)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq d hdq) with h1 | h2
    · omega
    · exact h2
