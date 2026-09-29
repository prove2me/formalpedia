-- Prove2me | solution 1 for Spike.Band.Extremal.compositionFactor_eq_max_iff_concentrated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:16.321736+00:00
-- url     : https://prove2.me/submissions/1928cf1b-4f5c-47e4-bdb6-657df015fdb9

-- Sol generated from Probability/SpikeCompositionExtremal.lean
import Mathlib
import Definitions.Def_Probability_SpikeBandComposition
import Definitions.Def_Probability_SpikeCompositionExtremal

/-!
# Extremal composition: how large a spike can pure band composition produce?

`Catalog/Probability/SpikeBandComposition.lean` proves the exact identity
`flatExcess = bandExcess + composition` and factorises the pooled rate ratio as
`(matched ratio) × (composition factor)`.  This file closes future direction 2
of `FUTURE_DIRECTIONS.md`: the *extremal* behaviour of the composition factor
over the exposure simplex.

Main results (`Spike.Band.Extremal`):

* `compositionFactor_le` / `compositionFactor_ge` : with band rates confined to
  `[pmin, pmax]`, the composition factor lies in `[pmin / p0, pmax / p0]`
  whatever the exposure allocation — the composition artifact is bounded by the
  *rate spread*, never by the sample size;
* `compositionFactor_eq_max_iff_concentrated` : the upper bound is attained
  exactly when all exposure sits on maximal-rate bands (a rigidity statement:
  any band carrying positive exposure must have `p i = pmax`);
* `exists_extremal_allocation` : the bound is attained, so it is sharp;
* `pooled_rateRatio_le_extremal` : the resulting universal ceiling
  `pooled ratio ≤ R * pmax / p0` on any size-matched analysis;
* `composition_le_spread` : the composition term itself is at most
  `(pmax - p0) * (total exposure)`;
* `round85_ceiling` : the reported numbers instantiated — with a flat null rate
  `p0 = 0.1`, band rates capped at `0.14924` and a matched within-band ratio
  capped at `1.097`, the pooled rate ratio cannot exceed `1.638`, which already
  covers the observed `1.637`.  No positional component is needed, and none can
  be inferred from the pooled ratio.

Interpretation: a "spike" of *any* size is reachable by composition alone once
the bands differ, but only in proportion to the rate spread — which the window
geometry (`Spike.size_residue_lt_96`) makes maximal, since the `bitlen ≥ 96`
band has mechanically zero first-decile rate.
-/

open Spike.Band.Extremal

open Spike.Band

variable {ι : Type*} (S : Finset ι) (n p : ι → ℝ) (p0 : ℝ)


variable {S n p p0}









open Spike.Band.Extremal in
theorem solution{pmax : ℝ} (hp0 : 0 < p0)
    (hn : ∀ i ∈ S, 0 ≤ n i) (hpmax : ∀ i ∈ S, p i ≤ pmax) (hpos : 0 < ∑ i ∈ S, n i)
    (heq : compositionFactor S n p p0 = pmax / p0) :
    ∀ i ∈ S, 0 < n i → p i = pmax := by
  have hsum : ∑ i ∈ S, p i * n i = pmax * ∑ i ∈ S, n i := by
    rw [compositionFactor] at heq
    field_simp at heq
    nlinarith [heq]
  have hzero : ∑ i ∈ S, (pmax - p i) * n i = 0 := by
    have : ∑ i ∈ S, (pmax - p i) * n i = pmax * (∑ i ∈ S, n i) - ∑ i ∈ S, p i * n i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsum]
    ring
  have hterm : ∀ i ∈ S, (pmax - p i) * n i = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hzero
    intro i hi
    exact mul_nonneg (by linarith [hpmax i hi]) (hn i hi)
  intro i hi hni
  have := hterm i hi
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h (ne_of_gt hni)
