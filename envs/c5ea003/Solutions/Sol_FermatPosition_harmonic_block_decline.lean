-- Prove2me | solution 1 for FermatPosition.harmonic_block_decline
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:23:43.949661+00:00
-- url     : https://prove2.me/submissions/435ab964-a019-4483-b380-69203e83b622

-- Sol generated from NumberTheory/FermatPositionDensity.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionDensity
import Definitions.Def_NumberTheory_FermatPositionGeometry
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
theorem solution(K : ℕ) (hK : 1 ≤ K) :
    ∑ j ∈ Icc (K + 1) (2 * K), (1 : ℚ) / j < ∑ j ∈ Icc 1 K, (1 : ℚ) / j := by
  have hcard : (Icc (K + 1) (2 * K)).card = K := by
    rw [Nat.card_Icc]; omega
  have hub : ∑ j ∈ Icc (K + 1) (2 * K), (1 : ℚ) / j ≤ (K : ℚ) * (1 / (K + 1)) := by
    have hterm : ∀ j ∈ Icc (K + 1) (2 * K), (1 : ℚ) / j ≤ 1 / (K + 1) := by
      intro j hj
      have hj1 : (K : ℚ) + 1 ≤ (j : ℚ) := by
        have := (mem_Icc.1 hj).1
        exact_mod_cast (by exact_mod_cast this : ((K : ℚ) + 1) ≤ (j : ℚ))
      have hpos : (0 : ℚ) < (K : ℚ) + 1 := by positivity
      exact one_div_le_one_div_of_le hpos hj1
    calc ∑ j ∈ Icc (K + 1) (2 * K), (1 : ℚ) / j
        ≤ ∑ _j ∈ Icc (K + 1) (2 * K), (1 : ℚ) / (K + 1) := Finset.sum_le_sum hterm
      _ = (K : ℚ) * (1 / (K + 1)) := by rw [Finset.sum_const, hcard]; simp [nsmul_eq_mul]
  have hlt : (K : ℚ) * (1 / (K + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  have hlb : (1 : ℚ) ≤ ∑ j ∈ Icc 1 K, (1 : ℚ) / j := by
    have hmem : (1 : ℕ) ∈ Icc 1 K := mem_Icc.2 ⟨le_rfl, hK⟩
    have hnonneg : ∀ j ∈ Icc 1 K, (0 : ℚ) ≤ 1 / j := by
      intro j _; positivity
    have := Finset.single_le_sum (f := fun j : ℕ => (1 : ℚ) / j) hnonneg hmem
    simpa using this
  linarith
