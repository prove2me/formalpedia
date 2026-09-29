-- Prove2me | Definitions.Def_Probability_RefractorySpikeTrains
-- name    : Probability_RefractorySpikeTrains
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:53.167636+00:00
-- url     : https://prove2.me/theorems/b9274866-54d8-4bd8-a5df-36112564db3e
-- title:
--   Aether Catalog definitions — Probability_RefractorySpikeTrains
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.RefractorySpikeTrains`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/RefractorySpikeTrains.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Probability.NeuralCoding.Temporal

open Finset

/-- The refractory relation on consecutive bins: two spikes may not be adjacent. -/
def NoAdj (a b : Bool) : Prop := ¬(a = true ∧ b = true)

instance : DecidableRel NoAdj := fun a b => by unfold NoAdj; infer_instance



/-- The admissible spike trains of a refractory neuron in a window of `n` bins,
built by the refractory recursion: a train either starts with a silent bin
followed by any admissible train of length `n - 1`, or starts with a spike,
which must be followed by a silent bin and then any admissible train of
length `n - 2`. -/
def trains : ℕ → Finset (List Bool)
  | 0 => {[]}
  | 1 => {[false], [true]}
  | (n + 2) =>
      (trains (n + 1)).image (fun l => false :: l) ∪
        (trains n).image (fun l => true :: false :: l)







end Catalog.Probability.NeuralCoding.Temporal


