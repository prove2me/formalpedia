-- Prove2me | solution 1 for RamseyBounds.hasSubFourUpperBound_of_polynomialLoss
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:33:08.917595+00:00
-- url     : https://prove2.me/submissions/8a3ebdad-4b3f-4ac9-b400-8572f69dfa24

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
theorem solution{r : ℕ → ℕ} (d : ℕ)
    {q : ℝ} (hq : 0 < q) (hq_lt_one : q < 1)
    (h : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (r k : ℝ) ≤ (k : ℝ) ^ d * (4 * q) ^ k) :
    HasSubFourUpperBound r := by
  let q' : ℝ := (q + 1) / 2
  have hq'_pos : 0 < q' := by
    dsimp [q']
    linarith
  have hq'_lt_one : q' < 1 := by
    dsimp [q']
    linarith
  have hbase : ‖(4 * q : ℝ)‖ < 4 * q' := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hq)]
    dsimp [q']
    linarith
  have hasym :=
    isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt d hbase
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      ‖(k : ℝ) ^ d * (4 * q) ^ k‖ ≤ 1 * ‖(4 * q') ^ k‖ :=
    hasym.bound zero_lt_one
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  obtain ⟨k₀, hk₀⟩ := h
  use 4 * (1 - q')
  refine ⟨by nlinarith, by nlinarith, max N k₀, ?_⟩
  intro k hk
  have hkN : N ≤ k := le_trans (le_max_left _ _) hk
  have hkk₀ : k₀ ≤ k := le_trans (le_max_right _ _) hk
  calc
    (r k : ℝ) ≤ (k : ℝ) ^ d * (4 * q) ^ k := hk₀ k hkk₀
    _ ≤ (4 * q') ^ k := by
      have hb := hN k hkN
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
        abs_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          (pow_nonneg (le_of_lt (mul_pos (by norm_num) hq)) _)),
        abs_of_nonneg
          (pow_nonneg (le_of_lt (mul_pos (by norm_num) hq'_pos)) _)] at hb
      exact hb
    _ = (4 - 4 * (1 - q')) ^ k := by ring_nf
