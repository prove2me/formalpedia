-- Prove2me | Theorems.Thm_FactoringLab_rational_escape_illusory
-- name    : FactoringLab.rational_escape_illusory
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:21.21001+00:00
-- url     : https://prove2.me/theorems/5d5bf5a2-74b2-47f2-92da-92393596a69d
-- title:
--   Rational escape is illusory (WWW).
-- statement:
--   **Rational escape is illusory (WWW).**  There is no rational function
--   `A/B` over `ℚ` that, evaluated at a semiprime `N = p*q` with `p < q` both
--   prime, returns the smaller prime factor `p`.  (The hypothesis includes that the
--   denominator does not vanish at the sample points, so the quotient is defined
--   there.)
--
--   ```lean
--   theorem FactoringLab.rational_escape_illusory(A B : Polynomial ℚ) :
--       ¬ ∀ p q : ℕ, p.Prime → q.Prime → p < q →
--           B.eval ((p * q : ℕ) : ℚ) ≠ 0 ∧
--             A.eval ((p * q : ℕ) : ℚ) = (p : ℚ) * B.eval ((p * q : ℕ) : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/FactoringBarriers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/FactoringBarriers.lean#L52

-- Thm stub generated from Probability/FactoringBarriers.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
/-
# Barriers I: the polynomial barrier, rational escape, holomorphic rigidity

Three of the eight barriers of the Factoring Lab framework, proved.

* `FactoringLab.polynomial_barrier` — no polynomial with rational coefficients
  computes the smaller prime factor of a semiprime.
* `FactoringLab.rational_escape_illusory` (WWW) — the same for *rational
  functions* `A/B`: passing from polynomials to quotients buys nothing.
* `FactoringLab.algebraic_barrier` — the strongest form: *no* nonzero
  polynomial relation `F(N, p) = 0` in two variables over `ℚ` holds for all
  semiprimes.  The polynomial and rational barriers are special cases.
* `FactoringLab.polynomial_barrier_counting` — a quantitative version: for a
  fixed small factor `p`, a polynomial of degree `d` can return the correct
  factor at no more than `d` semiprimes `pq`.
* `FactoringLab.holomorphic_rigidity` / `holomorphic_rigidity_barrier` (HRB) —
  an entire function that reproduces the reciprocal of the smaller prime factor
  at the reciprocals of semiprimes is forced by the identity theorem to be
  constant, which is impossible.

The proofs share one mechanism: fixing the small factor makes the sample set
accumulate (at infinity for polynomials, at `0` for the holomorphic version),
and rigidity of the function class then forces a constant, which two different
choices of the small factor contradict.
-/

open FactoringLab

open Polynomial Filter Set

/-! ### Arithmetic input: infinitely many primes above any bound -/



/-! ### The polynomial and rational barriers -/

theorem FactoringLab.rational_escape_illusory(A B : Polynomial ℚ) :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p < q →
        B.eval ((p * q : ℕ) : ℚ) ≠ 0 ∧
          A.eval ((p * q : ℕ) : ℚ) = (p : ℚ) * B.eval ((p * q : ℕ) : ℚ) := by sorry
