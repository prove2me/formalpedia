-- Prove2me | Definitions.Def_NumberTheory_FermatPositionDensity
-- name    : NumberTheory_FermatPositionDensity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:10.081992+00:00
-- url     : https://prove2.me/theorems/b700d5c5-7860-4db8-bab8-50057f23a8f0
-- title:
--   Aether Catalog definitions — NumberTheory_FermatPositionDensity
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.FermatPositionDensity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/FermatPositionDensity.lean by skeleton subtraction
import Mathlib
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

namespace FermatPosition

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

/-- The number of positions in `[a, a + L)` satisfying a position predicate. -/
def posCount (P : ℤ → Prop) [DecidablePred P] (a : ℤ) (L : ℕ) : ℕ :=
  ((range L).filter (fun i : ℕ => P (a + (i : ℤ)))).card






/-! ## The competing magnitude law -/







end FermatPosition


