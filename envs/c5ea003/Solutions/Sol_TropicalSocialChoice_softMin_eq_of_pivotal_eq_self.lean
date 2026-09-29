-- Prove2me | solution 1 for TropicalSocialChoice.softMin_eq_of_pivotal_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:02:25.286926+00:00
-- url     : https://prove2.me/submissions/dd6c0fdd-ae9c-4e49-b72c-243021a4882a

-- Sol generated from Probability/TropicalSocialChoiceDequantisation.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice V: exponentially sharp Maslov dequantisation

`Probability.TropicalSocialChoice` proved the crude two-sided bound
`min y − log (#s)/t ≤ softMin s t y ≤ min y` for the Boltzmann aggregator
`softMin s t y = −(1/t) log ∑_{i ∈ s} exp (−t yᵢ)`, and
`Probability.TropicalSocialChoiceOligarchy` sharpened the upper bound to
`softMin s t y ≤ min y − log m / t`, where `m` is the number of *pivotal* (cost-minimising)
voters.

Conjecture 2 of `FUTURE_DIRECTIONS.md` asserted that `m`, not `#s`, controls **both** sides,
the remaining error being exponentially small in the gap `Δ` between the minimal cost and
the next one.  This file proves it.

## Main results

* `softMin_ge_of_gap` : if every non-pivotal member of the coalition has cost at least
  `min y + Δ`, then
  `min y − log m / t − (q/m)·e^{−tΔ}/t ≤ softMin s t y`, where `q = #(s \ pivotal)`.
* `softMin_sandwich_of_gap` : combining with the proved upper bound,
  `0 ≤ (min y − log m / t) − softMin s t y ≤ (q/m)·e^{−tΔ}/t`.
* `softMin_error_le_exp` : for `t ≥ 1` the error is at most `(#s)·e^{−tΔ}`, i.e. the
  conjectured form `C e^{−tΔ}` with `C` depending only on `#s`.
* `exists_gap` : the gap hypothesis is never vacuous — whenever some member of the
  coalition is not pivotal, a strictly positive `Δ` with that property exists.
* `softMin_eq_of_pivotal_eq_self` : when *all* members are pivotal the Boltzmann value is
  exactly `min y − log (#s)/t`, so the `log m / t` term of the upper bound cannot be
  improved.
* `softMin_tendsto_exp_error` : the rescaled error `e^{tΔ/2}·(error)` tends to `0`, the
  quantitative form of the zero-temperature limit.
-/

open TropicalSocialChoice

open Finset Filter


variable {ι : Type*} [DecidableEq ι]









open TropicalSocialChoice in
omit [DecidableEq ι] in
theorem solution(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t : ℝ}
    (ht : 0 < t) (hall : pivotal s hs y = s) :
    softMin s t y = s.inf' hs y - Real.log s.card / t := by
  classical
  have hy : ∀ i ∈ s, y i = s.inf' hs y := by
    intro i hi
    have : i ∈ pivotal s hs y := by rw [hall]; exact hi
    exact (Finset.mem_filter.mp this).2
  have hsum : ∑ i ∈ s, Real.exp (-(t * y i)) = (s.card : ℝ) * Real.exp (-(t * s.inf' hs y)) := by
    rw [Finset.sum_congr rfl fun i hi => by rw [hy i hi]]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  rw [softMin, hsum, Real.log_mul (ne_of_gt hcard) (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  ring
