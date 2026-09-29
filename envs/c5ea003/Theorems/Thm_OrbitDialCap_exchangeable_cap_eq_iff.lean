-- Prove2me | Theorems.Thm_OrbitDialCap_exchangeable_cap_eq_iff
-- name    : OrbitDialCap.exchangeable_cap_eq_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:22.71265+00:00
-- url     : https://prove2.me/theorems/1f0f297e-7351-4e36-9e0a-9679509ddf6a
-- title:
--   The exchangeable cap is attained exactly at retention `θ = 1/2`, the value used in
-- statement:
--   The exchangeable cap is attained exactly at retention `θ = 1/2`, the value used in
--   the experiment (`RAND-MATCH 1.3387`, predicted `4/3 = 1.3333`).
--
--   ```lean
--   theorem OrbitDialCap.exchangeable_cap_eq_iff{θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
--       dialSpeedup θ θ = 4 / 3 ↔ θ = 1 / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/OrbitDialCapLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/OrbitDialCapLaw.lean#L95

-- Thm stub generated from Tropical/OrbitDialCapLaw.lean
import Mathlib
import Definitions.Def_Tropical_OrbitDialCapLaw

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

open OrbitDialCap

open Real

theorem OrbitDialCap.exchangeable_cap_eq_iff{θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    dialSpeedup θ θ = 4 / 3 ↔ θ = 1 / 2 := by sorry
