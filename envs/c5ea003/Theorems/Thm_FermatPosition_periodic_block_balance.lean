-- Prove2me | Theorems.Thm_FermatPosition_periodic_block_balance
-- name    : FermatPosition.periodic_block_balance
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:28:48.097309+00:00
-- url     : https://prove2.me/theorems/0e9f0804-ebe4-4dbb-8b86-3501d066fd11
-- title:
--   No local carrier can produce a large positional excess.
-- statement:
--   **No local carrier can produce a large positional excess.**  For a `T`-periodic
--   position predicate, the counts in any two windows of the same length `L = T * m + r`
--   differ by at most `T`.  Contrapositive: an observed excess of `E` hits of one block over
--   an equally long block rules out every carrier of modulus `T < E`.
--
--   ```lean
--   theorem FermatPosition.periodic_block_balance(T : ℕ) [NeZero T] (P : ℤ → Prop) [DecidablePred P]
--       (Q : ZMod T → Prop) [DecidablePred Q] (hPQ : ∀ j : ℤ, P j ↔ Q (j : ZMod T)) (a a' : ℤ)
--       (m r : ℕ) (hr : r < T) :
--       posCount P a (T * m + r) ≤ posCount P a' (T * m + r) + T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/FermatPositionDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/FermatPositionDensity.lean#L223

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




/-! ## Discrepancy of local (periodic) carriers

The general principle behind `FermatPosition.gcd_carrier_window_card_indep`: a carrier
that is *local*, i.e. determined by the position modulo some fixed `T`, has a bounded
discrepancy in every window.  It can never produce more than `T` excess hits between two
consecutive blocks of equal length.  Contrapositively, an observed positional excess of
`E` hits between consecutive equal blocks forces **every** local explanation to have
modulus `T ≥ E`. -/

theorem FermatPosition.periodic_block_balance(T : ℕ) [NeZero T] (P : ℤ → Prop) [DecidablePred P]
    (Q : ZMod T → Prop) [DecidablePred Q] (hPQ : ∀ j : ℤ, P j ↔ Q (j : ZMod T)) (a a' : ℤ)
    (m r : ℕ) (hr : r < T) :
    posCount P a (T * m + r) ≤ posCount P a' (T * m + r) + T := by sorry
