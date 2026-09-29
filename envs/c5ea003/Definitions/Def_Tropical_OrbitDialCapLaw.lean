-- Prove2me | Definitions.Def_Tropical_OrbitDialCapLaw
-- name    : Tropical_OrbitDialCapLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:15.275563+00:00
-- url     : https://prove2.me/theorems/d2b437b8-9cf5-4187-9212-33d10d67b86f
-- title:
--   Aether Catalog definitions — Tropical_OrbitDialCapLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.OrbitDialCapLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/OrbitDialCapLaw.lean by skeleton subtraction
import Mathlib

/-!
# The filter cap law: `4/3` for exchangeable dials, `1/θ` for structural ones

This file formalises the *filter accounting* underlying the ORBIT-DIAL-CAP-TEST
(FACT round-74 #2, exp 564).

## The cost model

We normalise the cost of an unfiltered `sqrt`-descending trial-division sweep to `1`.
A *dial* is a rule that retains a fraction `θ ∈ (0,1]` of the candidate divisors and
retains the *true* factor with probability `s ∈ [0,1]` (`s` is the dial's *soundness*).

Running the dial costs `θ` (the filtered sweep).  With probability `s` the factor is
inside the retained set and the search stops there; with probability `1 - s` the dial
missed and the remaining `1 - θ` candidates must still be swept, for total cost `1`.
Hence the expected cost is

`dialCost s θ = s * θ + (1 - s) * 1 = 1 - s + s * θ`

and the speedup over the unfiltered sweep is `dialSpeedup s θ = (dialCost s θ)⁻¹`.

## Main results

* `OrbitDialCap.exchangeable_cap` — an **exchangeable** dial (`s = θ`: the true factor
  is no more likely to be retained than any other candidate) has speedup `≤ 4/3`.
  This is *barrier 4*.
* `OrbitDialCap.exchangeable_cap_eq_iff` — the cap is attained exactly at `θ = 1/2`,
  matching the measured RAND-MATCH read `1.3387 ≈ 4/3`.
* `OrbitDialCap.speedup_gt_four_thirds_iff` — the cap is broken **iff** `s * (1-θ) > 1/4`,
  a clean threshold that separates the two regimes.
* `OrbitDialCap.soundness_excess_of_gt_cap` — quantitative escape cost: breaking the cap
  forces a strictly super-exchangeable soundness, `s - θ > (1 - 2θ)^2 / (4 (1-θ))`.
* `OrbitDialCap.deterministic_escape` and `OrbitDialCap.parity_skip_speedup` — a
  *deterministic* exclusion (`s = 1`) has speedup `1/θ`, equal to `2` at `θ = 1/2`:
  the ORBIT arm's `2.0000` read is exactly this, a constant shave, not a barrier event.
-/

namespace OrbitDialCap

open Real

/-- Expected cost of a filtered `sqrt`-descending sweep, normalised so that the
unfiltered sweep costs `1`.  `θ` is the retained fraction of candidates, `s` the
probability that the true factor survives the filter. -/
noncomputable def dialCost (s θ : ℝ) : ℝ := 1 - s + s * θ

/-- Speedup of a dial with soundness `s` and retention `θ` over the unfiltered sweep. -/
noncomputable def dialSpeedup (s θ : ℝ) : ℝ := (dialCost s θ)⁻¹



















end OrbitDialCap


