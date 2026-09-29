-- Prove2me | Theorems.Thm_Spike_Band_flatExcess_eq
-- name    : Spike.Band.flatExcess_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:06:10.27871+00:00
-- url     : https://prove2.me/theorems/91bc3dc6-26e4-4834-bdf9-acf4e3966ea7
-- title:
--   Exact excess decomposition.
-- statement:
--   **Exact excess decomposition.**  The flat-referenced excess is the sum of the
--   within-band rate excess and the composition term.  No assumptions.
--
--   ```lean
--   theorem Spike.Band.flatExcess_eq:
--       flatExcess S k n p0 = bandExcess S k n p + composition S n p p0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SpikeBandComposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SpikeBandComposition.lean#L57

-- Thm stub generated from Probability/SpikeBandComposition.lean
import Mathlib
import Definitions.Def_Probability_SpikeBandComposition

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

open Spike.Band

variable {ι : Type*} (S : Finset ι) (k n p : ι → ℝ) (p0 : ℝ)

theorem Spike.Band.flatExcess_eq:
    flatExcess S k n p0 = bandExcess S k n p + composition S n p p0 := by sorry
