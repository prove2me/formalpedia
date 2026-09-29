-- Prove2me | Theorems.Thm_FactoringLab_polynomial_barrier_of_algebraic
-- name    : FactoringLab.polynomial_barrier_of_algebraic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:53.007909+00:00
-- url     : https://prove2.me/theorems/0c13c53d-9aef-4c2c-9d4a-38f66463be1d
-- title:
--   The polynomial barrier is a special case of the algebraic barrier: the
-- statement:
--   The polynomial barrier is a special case of the algebraic barrier: the
--   degree-one relation `Y = P(X)` is excluded.
--
--   ```lean
--   theorem FactoringLab.polynomial_barrier_of_algebraic(P : Polynomial ℚ) :
--       ¬ ∀ p q : ℕ, p.Prime → q.Prime → p < q → P.eval ((p * q : ℕ) : ℚ) = (p : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/FactoringBarriers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/FactoringBarriers.lean#L150

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




/-! ### The algebraic barrier: no algebraic relation between `N` and `p` -/

theorem FactoringLab.polynomial_barrier_of_algebraic(P : Polynomial ℚ) :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p < q → P.eval ((p * q : ℕ) : ℚ) = (p : ℚ) := by sorry
