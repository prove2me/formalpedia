-- Prove2me | solution 1 for OrbitDialCap.exchangeable_cap_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:17:33.617778+00:00
-- url     : https://prove2.me/submissions/0543320b-5fdf-4772-bf66-ed54eb284953

-- Sol generated from Tropical/OrbitDialCapLaw.lean
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






/-- The expected cost is positive as soon as some candidates are retained. -/
lemma dialCost_pos {s θ : ℝ} (hs1 : s ≤ 1) (hs0 : 0 ≤ s) (hθ : 0 < θ) :
    0 < dialCost s θ := by
  rcases eq_or_lt_of_le hs1 with h | h
  · rw [dialCost, h]; linarith
  · have h1 : 0 < 1 - s := by linarith
    have h2 : 0 ≤ s * θ := mul_nonneg hs0 hθ.le
    simp only [dialCost]
    linarith
















open OrbitDialCap in
theorem solution{θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    dialSpeedup θ θ = 4 / 3 ↔ θ = 1 / 2 := by
  have hpos : 0 < dialCost θ θ := dialCost_pos hθ1 hθ.le hθ
  constructor
  · intro h
    have hcost : dialCost θ θ = 3 / 4 := by
      have := congrArg (fun x : ℝ => x⁻¹) h
      simpa [dialSpeedup, inv_inv, hpos.ne'] using this
    have hsq : (θ - 1 / 2) ^ 2 = 0 := by
      have : dialCost θ θ - 3 / 4 = (θ - 1 / 2) ^ 2 := by simp only [dialCost]; ring
      linarith [this, hcost]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith
  · rintro rfl
    norm_num [dialSpeedup, dialCost]
