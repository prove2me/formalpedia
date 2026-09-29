-- Prove2me | Theorems.Thm_FactoringBarriers_congruence_of_squares
-- name    : FactoringBarriers.congruence_of_squares
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:50:05.426531+00:00
-- url     : https://prove2.me/theorems/50d2b561-08fd-466b-ae8c-a86e9f86caec
-- title:
--   Congruence of squares.
-- statement:
--   **Congruence of squares.** If `N > 1` divides `(x - y)(x + y)` but divides
--   neither `x - y` nor `x + y`, then `gcd(x - y, N)` is a nontrivial divisor of `N`.
--
--   This is the unconditional engine of every sieve-based factoring method.
--
--   ```lean
--   theorem FactoringBarriers.congruence_of_squares{N : ℕ} (hN : 1 < N) {x y : ℤ}
--       (hsq : (N : ℤ) ∣ (x - y) * (x + y))
--       (hm : ¬ (N : ℤ) ∣ (x - y)) (hp : ¬ (N : ℤ) ∣ (x + y)) :
--       NontrivialDivisor N (Int.gcd (x - y) (N : ℤ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/CongruenceOfSquares.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/CongruenceOfSquares.lean#L41

-- Thm stub generated from Cryptography/FactoringBarriers/CongruenceOfSquares.lean
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

theorem FactoringBarriers.congruence_of_squares{N : ℕ} (hN : 1 < N) {x y : ℤ}
    (hsq : (N : ℤ) ∣ (x - y) * (x + y))
    (hm : ¬ (N : ℤ) ∣ (x - y)) (hp : ¬ (N : ℤ) ∣ (x + y)) :
    NontrivialDivisor N (Int.gcd (x - y) (N : ℤ)) := by sorry
