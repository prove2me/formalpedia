-- Prove2me | solution 1 for TropicalSocialChoice.softMin_error_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:06:12.283332+00:00
-- url     : https://prove2.me/submissions/cdaafad9-4c2b-4d3d-98b4-bbb2ff4f6985

-- Sol generated from Probability/TropicalSocialChoiceDequantisation.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Theorems.Thm_TropicalSocialChoice_pivotal_nonempty
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
theorem solution(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t Δ : ℝ}
    (ht : 1 ≤ t) (hgap : ∀ i ∈ s, i ∉ pivotal s hs y → s.inf' hs y + Δ ≤ y i) :
    (s.inf' hs y - Real.log (pivotal s hs y).card / t) - softMin s t y
      ≤ (s.card : ℝ) * Real.exp (-(t * Δ)) := by
  classical
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hmain := (softMin_sandwich_of_gap s hs y ht0 hgap).2
  set P := pivotal s hs y with hP
  have hPne : P.Nonempty := pivotal_nonempty s hs y
  have hppos : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hPne
  have hp1 : (1 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hPne
  have hqs : ((s \ P).card : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
  have hEpos : (0 : ℝ) < Real.exp (-(t * Δ)) := Real.exp_pos _
  have hden : (1 : ℝ) ≤ (P.card : ℝ) * t := by nlinarith
  have hstep : ((s \ P).card : ℝ) * Real.exp (-(t * Δ)) / ((P.card : ℝ) * t)
      ≤ (s.card : ℝ) * Real.exp (-(t * Δ)) := by
    rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < (P.card : ℝ) * t)]
    nlinarith [mul_nonneg (Nat.cast_nonneg (s.card)) hEpos.le]
  linarith
