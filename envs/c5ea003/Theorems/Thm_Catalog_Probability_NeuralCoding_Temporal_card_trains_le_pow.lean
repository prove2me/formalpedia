-- Prove2me | Theorems.Thm_Catalog_Probability_NeuralCoding_Temporal_card_trains_le_pow
-- name    : Catalog.Probability.NeuralCoding.Temporal.card_trains_le_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:01:30.644893+00:00
-- url     : https://prove2.me/theorems/dfe0fe64-2016-4803-bacc-8454c5691b6c
-- title:
--   Rate bound.
-- statement:
--   **Rate bound.**  The capacity of a `5m`-bin refractory window is at most
--   `16 ^ m`: the temporal code carries at most `4/5` of a bit per time bin,
--   strictly less than the `1` bit per bin of an unconstrained binary channel.
--
--   ```lean
--   theorem Catalog.Probability.NeuralCoding.Temporal.card_trains_le_pow: ∀ m : ℕ, (trains (5 * m)).card ≤ 16 ^ m
--     := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/RefractorySpikeTrains.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/RefractorySpikeTrains.lean#L176

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

theorem Catalog.Probability.NeuralCoding.Temporal.card_trains_le_pow: ∀ m : ℕ, (trains (5 * m)).card ≤ 16 ^ m
  := by sorry
