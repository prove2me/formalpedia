-- Prove2me | Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trains_lt_two_pow
-- name    : Catalog.Probability.NeuralCoding.Temporal.card_trains_lt_two_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:01:27.936144+00:00
-- url     : https://prove2.me/theorems/795e06d4-b011-4637-9ef8-a2ccd8220019
-- title:
--   The refractory constraint is a strict capacity loss: for windows of at least
-- statement:
--   The refractory constraint is a strict capacity loss: for windows of at least
--   two bins the refractory capacity is strictly below the unconstrained `2 ^ T`.
--
--   ```lean
--   theorem Catalog.Probability.NeuralCoding.Temporal.card_trains_lt_two_pow(n : ℕ) (hn : 2 ≤ n) : (trains n).card < 2 ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/RefractorySpikeTrains.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/RefractorySpikeTrains.lean#L143

-- Thm stub generated from Probability/RefractorySpikeTrains.lean
import Mathlib
import Definitions.Def_Probability_RefractorySpikeTrains
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Temporal neural codes: finite-window capacity under a refractory period

`Catalog/Novelty/NeuralCoding.lean` codes a concept by a single Boolean pattern
across neurons.  A *temporal* code instead uses the spike train of one neuron
across a window of `T` discrete time bins.  Biophysics forbids two spikes in
consecutive bins (the absolute refractory period), so the admissible spike
trains are exactly the binary words of length `T` with no two adjacent `true`s.

## Results

1. `trains` — the finset of admissible spike trains in a window of `T` bins,
   defined by the refractory recursion, and `mem_trains_iff`, which proves that
   this finset is *exactly* the set of length-`T` words with no two adjacent
   spikes.
2. `card_trains` — **finite-window capacity**: a refractory neuron has exactly
   `fib (T + 2)` distinguishable spike trains in `T` bins.
3. `card_trains_lt_two_pow` — the refractory constraint is a strict loss:
   capacity is `< 2 ^ T` for `T ≥ 2`.
4. `fib_five_step` / `card_trains_le_pow` — a quantitative rate bound:
   the capacity of a `5m`-bin window is at most `16 ^ m`, i.e. the temporal
   code carries at most `4/5` of a bit per time bin.
5. `temporal_rate_le` — the same statement in bits.
-/

open Catalog.Probability.NeuralCoding.Temporal

open Finset


instance : DecidableRel NoAdj := fun a b => by unfold NoAdj; infer_instance

theorem Catalog.Probability.NeuralCoding.Temporal.card_trains_lt_two_pow(n : ℕ) (hn : 2 ≤ n) : (trains n).card < 2 ^ n := by sorry
