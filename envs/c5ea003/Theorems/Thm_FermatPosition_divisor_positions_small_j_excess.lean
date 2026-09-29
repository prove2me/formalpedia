-- Prove2me | Theorems.Thm_FermatPosition_divisor_positions_small_j_excess
-- name    : FermatPosition.divisor_positions_small_j_excess
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:28:45.735274+00:00
-- url     : https://prove2.me/theorems/de6ae38b-3d2c-46ff-812d-32241ff796ad
-- title:
--   Proved small-`j` excess of the self-divisibility carrier.
-- statement:
--   **Proved small-`j` excess of the self-divisibility carrier.**  Average over a window
--   of base values `v(0)` whose length `M` is divisible by every `j ≤ 2K` (so that all the
--   densities are exact).  Then the expected number of positions `j` in `[1, K]` at which
--   `j ∣ v(j)` strictly exceeds the expected number in the next block `(K, 2K]`.  Unlike the
--   gcd carrier (`gcd_carrier_window_card_indep`) this carrier really does prefer small
--   positions, with the harmonic `1/j` profile.
--
--   ```lean
--   theorem FermatPosition.divisor_positions_small_j_excess(K : ℕ) (hK : 1 ≤ K) (M : ℕ) (hM0 : 0 < M)
--       (hM : ∀ j ∈ Icc 1 (2 * K), j ∣ M) (a : ℤ) :
--       ∑ j ∈ Icc (K + 1) (2 * K),
--           (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ)
--         < ∑ j ∈ Icc 1 K, (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/FermatPositionDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/FermatPositionDensity.lean#L113

-- Thm stub generated from NumberTheory/FermatPositionDensity.lean
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

theorem FermatPosition.divisor_positions_small_j_excess(K : ℕ) (hK : 1 ≤ K) (M : ℕ) (hM0 : 0 < M)
    (hM : ∀ j ∈ Icc 1 (2 * K), j ∣ M) (a : ℤ) :
    ∑ j ∈ Icc (K + 1) (2 * K),
        (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ)
      < ∑ j ∈ Icc 1 K, (((range M).filter (fun i : ℕ => (j : ℤ) ∣ (a + i))).card : ℚ) := by sorry
