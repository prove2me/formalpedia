-- Prove2me | Theorems.Thm_FactoringBarriers_nontrivialDivisor_semiprime
-- name    : FactoringBarriers.nontrivialDivisor_semiprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:50:20.996221+00:00
-- url     : https://prove2.me/theorems/17c71431-cba0-4982-817a-fc621b049e1f
-- title:
--   For a semiprime `N = p q`, every nontrivial divisor is one of the two prime
-- statement:
--   For a semiprime `N = p q`, every nontrivial divisor is one of the two prime
--   factors: exhibiting *any* nontrivial divisor is the same as factoring.
--
--   ```lean
--   theorem FactoringBarriers.nontrivialDivisor_semiprime{p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (h : NontrivialDivisor (p * q) d) : d = p ∨ d = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/CongruenceOfSquares.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/CongruenceOfSquares.lean#L85

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



/-! ## For semiprimes the structural step is everything -/

theorem FactoringBarriers.nontrivialDivisor_semiprime{p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : NontrivialDivisor (p * q) d) : d = p ∨ d = q := by sorry
