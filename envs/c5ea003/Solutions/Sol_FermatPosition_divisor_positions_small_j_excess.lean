-- Prove2me | solution 1 for FermatPosition.divisor_positions_small_j_excess
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:27:58.143468+00:00
-- url     : https://prove2.me/submissions/3a530df0-01d1-4fd2-a0af-fcf456110f13

-- Sol generated from NumberTheory/FermatPositionDensity.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionDensity
import Definitions.Def_NumberTheory_FermatPositionGeometry
import Theorems.Thm_FermatPosition_card_filter_dvd
import Theorems.Thm_FermatPosition_harmonic_block_decline
/-
# Densities of the two position carriers of the Fermat / quadratic-sieve polynomial

Companion to `Catalog/NumberTheory/FermatPositionGeometry.lean`.

That file isolated two magnitude-free ("beyond-magnitude") arithmetic mechanisms that
could bias where the smooth values of `v(j) = (b + j)^2 - N` sit:

* the **gcd carrier** `g(j) = gcd (j, v(0))`, which is *positionally uniform*
  (`FermatPosition.gcd_carrier_window_card_indep`), so it enriches smoothness without
  favouring any position; and
* the **self-divisibility carrier** `j ∣ v(j) ↔ j ∣ v(0)`, whose density at position
  `j` is exactly `1/j`.

This file proves the quantitative half of the story.

Main results.

* `dvd_window_card_eq_one`, `card_filter_dvd` : exactly one multiple of `d` in every
  window of `d` consecutive integers, hence exactly `t` in a window of length `d * t`;
  the self-divisibility carrier has density exactly `1/j` at position `j`.
* `harmonic_block_decline` : `∑_{K < j ≤ 2K} 1/j < ∑_{1 ≤ j ≤ K} 1/j` for `K ≥ 1`.
* `divisor_positions_small_j_excess` : consequently, averaged over base values `v(0)`,
  the expected number of positions `j ≤ K` with `j ∣ v(j)` **strictly exceeds** the
  expected number in the next block `K < j ≤ 2K`.  A proved, magnitude-free, small-`j`
  excess — the shape of the empirically observed monotone-declining deciles.
* `sieveVal_sandwich` and `position_le_of_value_le` : the competing *magnitude* law,
  `2 b j ≤ v(j) ≤ 2 b j + j² + 2 b`, so a bound on the value forces a bound on the
  position (`j ≤ X / (2b)`).  This is what a positional test has to be controlled
  against, and by `FermatPosition.cell_collapse` bit-length cells do not control it.
-/

open FermatPosition

open Finset

/-! ## Exact density of the self-divisibility carrier -/



/-! ## The harmonic decline of the divisor-position profile -/




/-! ## Discrepancy of local (periodic) carriers

The general principle behind `FermatPosition.gcd_carrier_window_card_indep`: a carrier
that is *local*, i.e. determined by the position modulo some fixed `T`, has a bounded
discrepancy in every window.  It can never produce more than `T` excess hits between two
consecutive blocks of equal length.  Contrapositively, an observed positional excess of
`E` hits between consecutive equal blocks forces **every** local explanation to have
modulus `T ≥ E`. -/







/-! ## The competing magnitude law -/








open FermatPosition in
theorem solution(K : ℕ) (hK : 1 ≤ K) (M : ℕ) (hM0 : 0 < M)
    (hM : ∀ j ∈ Icc 1 (2 * K), j ∣ M) (a : ℤ) :
    ∑ j ∈ Icc (K + 1) (2 * K),
        (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ)
      < ∑ j ∈ Icc 1 K, (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ) := by
  have key : ∀ j ∈ Icc 1 (2 * K),
      (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ) = (M : ℚ) * (1 / j) := by
    intro j hj
    have hj1 : 0 < j := (mem_Icc.1 hj).1
    obtain ⟨t, ht⟩ := hM j hj
    have hcard : ((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card = t := by
      rw [ht]; exact card_filter_dvd j hj1 t a
    rw [hcard, ht]
    have hjQ : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast
    field_simp
  have h₁ : ∑ j ∈ Icc (K + 1) (2 * K),
      (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ)
      = (M : ℚ) * ∑ j ∈ Icc (K + 1) (2 * K), (1 : ℚ) / j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => key j ?_
    have := mem_Icc.1 hj
    exact mem_Icc.2 ⟨by omega, this.2⟩
  have h₂ : ∑ j ∈ Icc 1 K, (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ)
      = (M : ℚ) * ∑ j ∈ Icc 1 K, (1 : ℚ) / j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => key j ?_
    have := mem_Icc.1 hj
    exact mem_Icc.2 ⟨this.1, by omega⟩
  rw [h₁, h₂]
  have hMpos : (0 : ℚ) < M := by exact_mod_cast hM0
  exact mul_lt_mul_of_pos_left (harmonic_block_decline K hK) hMpos
