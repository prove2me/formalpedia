-- Prove2me | Theorems.Thm_RamseyBounds_hasSubFourUpperBound_of_polynomialLoss
-- name    : RamseyBounds.hasSubFourUpperBound_of_polynomialLoss
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:29:09.006644+00:00
-- url     : https://prove2.me/theorems/1b55ff82-eca3-44c1-b3af-9270e75de50d
-- title:
--   A fixed polynomial loss does not destroy a strict exponential saving.
-- statement:
--   A fixed polynomial loss does not destroy a strict exponential saving.
--
--   More precisely, if `r k` is eventually at most `k^d (4q)^k` for one fixed
--   `q ∈ (0,1)`, then it is eventually bounded by `(4-ε)^k` for a fixed positive
--   `ε`.  The proof absorbs the polynomial into the larger saving factor
--   `q' = (q+1)/2`, which is still strictly below one.
--
--   ```lean
--   theorem RamseyBounds.hasSubFourUpperBound_of_polynomialLoss{r : ℕ → ℕ} (d : ℕ)
--       {q : ℝ} (hq : 0 < q) (hq_lt_one : q < 1)
--       (h : ∃ k₀ : ℕ, ∀ k ≥ k₀,
--         (r k : ℝ) ≤ (k : ℝ) ^ d * (4 * q) ^ k) :
--       HasSubFourUpperBound r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/RamseyExponentialBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/RamseyExponentialBounds.lean#L100

-- Thm stub generated from Combinatorics/RamseyExponentialBounds.lean
import Mathlib
import Definitions.Def_Combinatorics_RamseyExponentialBounds

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

open RamseyBounds

theorem RamseyBounds.hasSubFourUpperBound_of_polynomialLoss{r : ℕ → ℕ} (d : ℕ)
    {q : ℝ} (hq : 0 < q) (hq_lt_one : q < 1)
    (h : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (r k : ℝ) ≤ (k : ℝ) ^ d * (4 * q) ^ k) :
    HasSubFourUpperBound r := by sorry
