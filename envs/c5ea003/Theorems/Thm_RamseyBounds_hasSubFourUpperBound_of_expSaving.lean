-- Prove2me | Theorems.Thm_RamseyBounds_hasSubFourUpperBound_of_expSaving
-- name    : RamseyBounds.hasSubFourUpperBound_of_expSaving
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:28:58.805116+00:00
-- url     : https://prove2.me/theorems/f1889426-e2ed-44c3-a28e-20cfe92a90e0
-- title:
--   An exponentially decaying correction to the base four gives an explicit
-- statement:
--   An exponentially decaying correction to the base four gives an explicit
--   sub-four gap `ε = 4(1-exp(-δ))`.
--
--   ```lean
--   theorem RamseyBounds.hasSubFourUpperBound_of_expSaving{r : ℕ → ℕ} {δ : ℝ} (hδ : 0 < δ)
--       (h : ∃ k₀ : ℕ, ∀ k ≥ k₀,
--         (r k : ℝ) ≤ (4 * Real.exp (-δ)) ^ k) :
--       HasSubFourUpperBound r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/RamseyExponentialBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/RamseyExponentialBounds.lean#L64

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

theorem RamseyBounds.hasSubFourUpperBound_of_expSaving{r : ℕ → ℕ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (r k : ℝ) ≤ (4 * Real.exp (-δ)) ^ k) :
    HasSubFourUpperBound r := by sorry
