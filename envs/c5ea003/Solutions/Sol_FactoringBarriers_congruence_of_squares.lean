-- Prove2me | solution 1 for FactoringBarriers.congruence_of_squares
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:36:14.848171+00:00
-- url     : https://prove2.me/submissions/d4fac4be-4ef4-4234-a9c0-d94f9a03447c

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
theorem solution{N : ℕ} (hN : 1 < N) {x y : ℤ}
    (hsq : (N : ℤ) ∣ (x - y) * (x + y))
    (hm : ¬ (N : ℤ) ∣ (x - y)) (hp : ¬ (N : ℤ) ∣ (x + y)) :
    NontrivialDivisor N (Int.gcd (x - y) (N : ℤ)) := by
  set d : ℕ := Int.gcd (x - y) (N : ℤ) with hd
  have hdvdN : d ∣ N := by
    have : (d : ℤ) ∣ (N : ℤ) := Int.gcd_dvd_right _ _
    exact_mod_cast this
  have hdvdxy : (d : ℤ) ∣ (x - y) := Int.gcd_dvd_left _ _
  have hdne1 : d ≠ 1 := by
    intro h1
    have hcop : IsCoprime (x - y) (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by rw [← hd, h1])
    have hcop' : IsCoprime (N : ℤ) (x - y) := hcop.symm
    exact hp (hcop'.dvd_of_dvd_mul_left hsq)
  have hdneN : d ≠ N := by
    intro hEq
    exact hm (by rw [← hEq] at *; exact_mod_cast hdvdxy)
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hdvdN
    exact absurd (Nat.eq_zero_of_zero_dvd hdvdN) (by omega)
  refine ⟨hdvdN, by omega, ?_⟩
  have hle : d ≤ N := Nat.le_of_dvd (by omega) hdvdN
  omega
