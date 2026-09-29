-- Prove2me | Definitions.Def_Combinatorics_RamseyExponentialBounds
-- name    : Combinatorics_RamseyExponentialBounds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:48:35.623742+00:00
-- url     : https://prove2.me/theorems/de0e7ff9-f27c-43e1-8e37-567b2a5cc8d9
-- title:
--   Aether Catalog definitions — Combinatorics_RamseyExponentialBounds
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.RamseyExponentialBounds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/RamseyExponentialBounds.lean by skeleton subtraction
import Mathlib

/-!
# Exponential bounds for diagonal Ramsey numbers: the analytic interface

This file isolates the final quantitative step used by sub-four diagonal Ramsey
bounds.  The combinatorial part of such an argument typically produces a fixed
multiplicative saving `q < 1` per clique size, giving a bound `(4q)^k`.  The
results below convert that estimate, without asymptotic notation, into the
standard form `(4 - ε)^k` with one fixed `ε > 0`.

The development is deliberately parameterized by the catalog's Ramsey-number
sequence: it makes no new graph or Ramsey-number definition.  Consequently the
lemmas can be applied directly to any existing encoding of diagonal Ramsey
numbers.
-/

namespace RamseyBounds

/-- A sequence has an eventual diagonal-Ramsey-style upper bound with base
strictly below four. -/
def HasSubFourUpperBound (r : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 4 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, (r k : ℝ) ≤ (4 - ε) ^ k

/-- A fixed proportional saving over the classical base four. -/
def HasProportionalSaving (r : ℕ → ℕ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, (r k : ℝ) ≤ (4 * q) ^ k








end RamseyBounds


