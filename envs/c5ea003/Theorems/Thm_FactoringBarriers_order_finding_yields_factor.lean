-- Prove2me | Theorems.Thm_FactoringBarriers_order_finding_yields_factor
-- name    : FactoringBarriers.order_finding_yields_factor
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:50:22.543214+00:00
-- url     : https://prove2.me/theorems/44ad5e72-de84-42b9-a87f-042409445a0c
-- title:
--   Order finding reduction (classical post-processing of Shor).
-- statement:
--   **Order finding reduction (classical post-processing of Shor).**
--   If `a` has an even multiplicative order `2s` modulo `N`, and `a^s ≢ ±1`, then
--   `gcd(a^s - 1, N)` is a nontrivial divisor of `N`.
--
--   ```lean
--   theorem FactoringBarriers.order_finding_yields_factor{N : ℕ} (hN : 1 < N) {a : ℤ} {s : ℕ}
--       (hord : (N : ℤ) ∣ a ^ (2 * s) - 1)
--       (hm : ¬ (N : ℤ) ∣ (a ^ s - 1)) (hp : ¬ (N : ℤ) ∣ (a ^ s + 1)) :
--       NontrivialDivisor N (Int.gcd (a ^ s - 1) (N : ℤ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FactoringBarriers/CongruenceOfSquares.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FactoringBarriers/CongruenceOfSquares.lean#L70

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

theorem FactoringBarriers.order_finding_yields_factor{N : ℕ} (hN : 1 < N) {a : ℤ} {s : ℕ}
    (hord : (N : ℤ) ∣ a ^ (2 * s) - 1)
    (hm : ¬ (N : ℤ) ∣ (a ^ s - 1)) (hp : ¬ (N : ℤ) ∣ (a ^ s + 1)) :
    NontrivialDivisor N (Int.gcd (a ^ s - 1) (N : ℤ)) := by sorry
