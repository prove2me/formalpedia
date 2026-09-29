-- Prove2me | Definitions.Def_Probability_SpikeBandComposition
-- name    : Probability_SpikeBandComposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:13.595418+00:00
-- url     : https://prove2.me/theorems/cf61357b-0ead-4135-93db-cd26ab45b5ba
-- title:
--   Aether Catalog definitions — Probability_SpikeBandComposition
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SpikeBandComposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SpikeBandComposition.lean by skeleton subtraction
import Mathlib

/-!
# Composition versus rate: exact accounting for a stratified edge excess

Companion to `Catalog/Probability/SpikeInclusionGeometry.lean`.  There we proved
that the first decile of the search window is, by exact arithmetic, a pure
tiny-`v` stratum.  Here we prove the statistical consequence: an excess measured
against a *flat* (size-blind) null splits **exactly** into

* a within-band *rate* term, and
* a *composition* term produced by the heterogeneity of band-specific rates.

The main identity is `Spike.Band.flatExcess_eq`:

`flatExcess = bandExcess + composition`,

with the two immediate boundary readings

* `flatExcess_eq_composition_of_matched` : if every band is size-matched
  (`k i = p i * n i`, i.e. within-band rate ratio `1`), the *entire* flat excess
  is composition;
* `composition_eq_zero_of_homogeneous` : if all bands share the flat rate, the
  composition term vanishes and flat excess = band excess.  So a composition
  artifact requires genuine band heterogeneity — exactly what the inclusion
  geometry supplies.

Quantitatively, `pooled_rateRatio_le` factorises the pooled rate ratio as
`(matched rate ratio) × (composition factor)`, and `rate_ratio_1637` is the
arithmetic instance matching the reported numbers: a matched ratio of `1.097`
times a composition factor of `1.4924` already exceeds the observed pooled
ratio `1.637`, leaving nothing for a positional component.

Finally `exists_pure_composition_spike` is an explicit two-band configuration —
a mechanically-zero-rate band (`bitlen ≥ 96`) and a tiny-`v` band — in which
every within-band rate ratio is exactly `1`, the band-referenced excess is
exactly `0`, and yet the flat-referenced excess exceeds `500` with pooled rate
ratio above `1.6`.  This is a Simpson-type reversal in the exact configuration
forced by the window geometry.
-/

namespace Spike.Band

variable {ι : Type*} (S : Finset ι) (k n p : ι → ℝ) (p0 : ℝ)

/-- Excess of the observed edge counts over a *flat* null with common rate
`p0`. -/
def flatExcess : ℝ := (∑ i ∈ S, k i) - p0 * ∑ i ∈ S, n i

/-- Excess of the observed edge counts over the *band-referenced* null, whose
rate in band `i` is `p i`. -/
def bandExcess : ℝ := ∑ i ∈ S, (k i - p i * n i)

/-- The composition term: how much the band-referenced null already exceeds the
flat null, purely because of how exposure is distributed across bands. -/
def composition : ℝ := ∑ i ∈ S, (p i - p0) * n i










end Spike.Band


