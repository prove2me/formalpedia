-- Prove2me | solution 1 for FactoringBarriers.order_finding_yields_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:37:34.48816+00:00
-- url     : https://prove2.me/submissions/3ef82303-935d-4d21-91a4-71e5624a08d9

-- Sol generated from Cryptography/FactoringBarriers/CongruenceOfSquares.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Theorems.Thm_FactoringBarriers_congruence_of_squares

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
theorem solution{N : ℕ} (hN : 1 < N) {a : ℤ} {s : ℕ}
    (hord : (N : ℤ) ∣ a ^ (2 * s) - 1)
    (hm : ¬ (N : ℤ) ∣ (a ^ s - 1)) (hp : ¬ (N : ℤ) ∣ (a ^ s + 1)) :
    NontrivialDivisor N (Int.gcd (a ^ s - 1) (N : ℤ)) := by
  refine congruence_of_squares hN ?_ hm hp
  have hrw : (a ^ s - 1) * (a ^ s + 1) = a ^ (2 * s) - 1 := by
    rw [two_mul, pow_add]; ring
  rw [hrw]
  exact hord
