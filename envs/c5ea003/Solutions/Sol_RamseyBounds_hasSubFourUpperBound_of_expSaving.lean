-- Prove2me | solution 1 for RamseyBounds.hasSubFourUpperBound_of_expSaving
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:33:08.234032+00:00
-- url     : https://prove2.me/submissions/b17b88a8-d4dc-4b9a-978a-44cfd62ce2cb

-- Sol generated from Combinatorics/RamseyExponentialBounds.lean
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











open RamseyBounds in
theorem solution{r : ℕ → ℕ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (r k : ℝ) ≤ (4 * Real.exp (-δ)) ^ k) :
    HasSubFourUpperBound r := by
  -- Set ε = 4 * (1 - exp(-δ))
  use 4 * (1 - Real.exp (-δ))
  -- Show ε > 0: since δ > 0, exp(-δ) < 1, so 1 - exp(-δ) > 0
  have hexp_lt_one : Real.exp (-δ) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos hδ
  have hε_pos : 0 < 4 * (1 - Real.exp (-δ)) := by linarith
  refine ⟨hε_pos, ?_, ?_⟩
  -- Show ε < 4: since exp(-δ) > 0, we have 1 - exp(-δ) < 1, so 4*(1 - exp(-δ)) < 4
  have hexp_pos : 0 < Real.exp (-δ) := Real.exp_pos _
  linarith
  -- Need to convert (4 * exp(-δ))^k to (4 - 4*(1 - exp(-δ)))^k
  obtain ⟨k₀, hk₀⟩ := h
  exact ⟨k₀, fun k hk => by
    have : (4 : ℝ) * Real.exp (-δ) = 4 - 4 * (1 - Real.exp (-δ)) := by ring
    rw [← this]
    exact hk₀ k hk⟩
