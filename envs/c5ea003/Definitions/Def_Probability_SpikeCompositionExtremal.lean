-- Prove2me | Definitions.Def_Probability_SpikeCompositionExtremal
-- name    : Probability_SpikeCompositionExtremal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:47.491871+00:00
-- url     : https://prove2.me/theorems/17e0910b-048e-417e-a1d9-a3e990af75fa
-- title:
--   Aether Catalog definitions — Probability_SpikeCompositionExtremal
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SpikeCompositionExtremal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SpikeCompositionExtremal.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_SpikeBandComposition

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

namespace Spike.Band.Extremal

open Spike.Band

variable {ι : Type*} (S : Finset ι) (n p : ι → ℝ) (p0 : ℝ)

/-- The composition factor: the band-referenced expectation divided by the flat
expectation.  This is the multiplicative form of `Spike.Band.composition`. -/
noncomputable def compositionFactor : ℝ := (∑ i ∈ S, p i * n i) / (p0 * ∑ i ∈ S, n i)

variable {S n p p0}








end Spike.Band.Extremal


