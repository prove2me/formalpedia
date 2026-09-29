-- Prove2me | solution 1 for TropicalSocialChoice.softMin_tendsto_exp_error
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:08:07.180619+00:00
-- url     : https://prove2.me/submissions/dabab0d8-5136-4dbd-8c44-17b93dbe337d

-- Sol generated from Probability/TropicalSocialChoiceDequantisation.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Theorems.Thm_TropicalSocialChoice_softMin_error_le_exp
import Theorems.Thm_TropicalSocialChoice_softMin_ge_of_gap
import Theorems.Thm_TropicalSocialChoice_softMin_le_sub_log_card_pivotal
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



/-- **Conjecture 2, proved.**  Two-sided exponentially sharp dequantisation: the Boltzmann
aggregator sits below the tropical value by exactly `log m / t`, up to an error that is
exponentially small in the cost gap. -/
theorem softMin_sandwich_of_gap (s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t Δ : ℝ}
    (ht : 0 < t) (hgap : ∀ i ∈ s, i ∉ pivotal s hs y → s.inf' hs y + Δ ≤ y i) :
    0 ≤ (s.inf' hs y - Real.log (pivotal s hs y).card / t) - softMin s t y ∧
      (s.inf' hs y - Real.log (pivotal s hs y).card / t) - softMin s t y
        ≤ ((s \ pivotal s hs y).card : ℝ) * Real.exp (-(t * Δ))
            / ((pivotal s hs y).card * t) := by
  have hup := softMin_le_sub_log_card_pivotal s hs y ht
  have hlow := softMin_ge_of_gap s hs y ht hgap
  exact ⟨by linarith, by linarith⟩






open TropicalSocialChoice in
theorem solution(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {Δ : ℝ}
    (hΔ : 0 < Δ) (hgap : ∀ i ∈ s, i ∉ pivotal s hs y → s.inf' hs y + Δ ≤ y i) :
    Tendsto (fun t : ℝ => Real.exp (t * Δ / 2) *
        ((s.inf' hs y - Real.log (pivotal s hs y).card / t) - softMin s t y))
      atTop (nhds 0) := by
  classical
  have hmaj : Tendsto (fun t : ℝ => (s.card : ℝ) * Real.exp (-(t * Δ / 2))) atTop (nhds 0) := by
    have h0 : Tendsto (fun t : ℝ => t * (Δ / 2)) atTop atTop :=
      Filter.Tendsto.atTop_mul_const (by positivity) Filter.tendsto_id
    have h1 : Tendsto (fun t : ℝ => -(t * Δ / 2)) atTop atBot :=
      (Filter.tendsto_neg_atTop_atBot.comp h0).congr fun t => by
        simp [Function.comp, mul_div_assoc]
    have h2 := Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul ((s.card : ℝ))
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
    have := (softMin_sandwich_of_gap s hs y ht0 hgap).1
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have herr := softMin_error_le_exp s hs y ht hgap
    have hpos : (0 : ℝ) < Real.exp (t * Δ / 2) := Real.exp_pos _
    calc Real.exp (t * Δ / 2) *
          ((s.inf' hs y - Real.log (pivotal s hs y).card / t) - softMin s t y)
        ≤ Real.exp (t * Δ / 2) * ((s.card : ℝ) * Real.exp (-(t * Δ))) := by
          exact mul_le_mul_of_nonneg_left herr hpos.le
      _ = (s.card : ℝ) * Real.exp (-(t * Δ / 2)) := by
          rw [show -(t * Δ) = -(t * Δ / 2) + -(t * Δ / 2) by ring, Real.exp_add]
          rw [show t * Δ / 2 = -(-(t * Δ / 2)) by ring, Real.exp_neg]
          field_simp
