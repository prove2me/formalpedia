-- Prove2me | solution 1 for TropicalSocialChoice.softMin_ge_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:04:26.382161+00:00
-- url     : https://prove2.me/submissions/0d9a04b3-e3dd-4694-8503-3c7a3b067f0d

-- Sol generated from Probability/TropicalSocialChoiceDequantisation.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Theorems.Thm_TropicalSocialChoice_pivotal_nonempty
import Theorems.Thm_TropicalSocialChoice_pivotal_subset
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
theorem solution(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t Δ : ℝ} (ht : 0 < t)
    (hgap : ∀ i ∈ s, i ∉ pivotal s hs y → s.inf' hs y + Δ ≤ y i) :
    s.inf' hs y - Real.log (pivotal s hs y).card / t
        - ((s \ pivotal s hs y).card : ℝ) * Real.exp (-(t * Δ))
          / ((pivotal s hs y).card * t) ≤ softMin s t y := by
  classical
  set mu := s.inf' hs y with hmu
  set P := pivotal s hs y with hP
  have hPs : P ⊆ s := pivotal_subset s hs y
  have hPne : P.Nonempty := pivotal_nonempty s hs y
  set p : ℝ := (P.card : ℝ) with hp
  set q : ℝ := ((s \ P).card : ℝ) with hq
  set E : ℝ := Real.exp (-(t * Δ)) with hE
  set e : ℝ := Real.exp (-(t * mu)) with he
  have hppos : 0 < p := by
    rw [hp]; exact_mod_cast Finset.card_pos.mpr hPne
  have hepos : 0 < e := Real.exp_pos _
  have hEpos : 0 < E := Real.exp_pos _
  have hqnonneg : 0 ≤ q := by rw [hq]; positivity
  -- the pivotal part of the sum
  have h1 : ∑ i ∈ P, Real.exp (-(t * y i)) = p * e := by
    rw [Finset.sum_congr rfl fun i hi => by
      rw [show y i = mu from (Finset.mem_filter.mp hi).2]]
    simp [Finset.sum_const, nsmul_eq_mul, hp, he]
  -- the non-pivotal part is exponentially smaller
  have h2 : ∑ i ∈ s \ P, Real.exp (-(t * y i)) ≤ q * (e * E) := by
    have hterm : ∀ i ∈ s \ P, Real.exp (-(t * y i)) ≤ e * E := by
      intro i hi
      obtain ⟨his, hiP⟩ := Finset.mem_sdiff.mp hi
      have hy : mu + Δ ≤ y i := hgap i his hiP
      have : -(t * y i) ≤ -(t * mu) + -(t * Δ) := by nlinarith
      calc Real.exp (-(t * y i)) ≤ Real.exp (-(t * mu) + -(t * Δ)) := Real.exp_le_exp.mpr this
        _ = e * E := by rw [Real.exp_add]
    calc ∑ i ∈ s \ P, Real.exp (-(t * y i)) ≤ ∑ _i ∈ s \ P, e * E := Finset.sum_le_sum hterm
      _ = q * (e * E) := by simp [Finset.sum_const, nsmul_eq_mul, hq]
  have hsplit : ∑ i ∈ s \ P, Real.exp (-(t * y i)) + ∑ i ∈ P, Real.exp (-(t * y i))
      = ∑ i ∈ s, Real.exp (-(t * y i)) := Finset.sum_sdiff hPs
  have hSpos : 0 < ∑ i ∈ s, Real.exp (-(t * y i)) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) hs
  have hSle : ∑ i ∈ s, Real.exp (-(t * y i)) ≤ e * (p + q * E) := by
    rw [← hsplit, h1]
    nlinarith [h2]
  -- take logarithms
  have hfac : 0 < p + q * E := by positivity
  have hlogS : Real.log (∑ i ∈ s, Real.exp (-(t * y i))) ≤ -(t * mu) + Real.log (p + q * E) := by
    have h := Real.log_le_log hSpos hSle
    rwa [Real.log_mul (ne_of_gt hepos) (ne_of_gt hfac), he, Real.log_exp] at h
  have hlogfac : Real.log (p + q * E) ≤ Real.log p + q * E / p := by
    have hfac' : p + q * E = p * (1 + q * E / p) := by field_simp
    have hx : (0 : ℝ) < 1 + q * E / p := by positivity
    have := Real.log_le_sub_one_of_pos hx
    rw [hfac', Real.log_mul (ne_of_gt hppos) (ne_of_gt hx)]
    linarith
  have hlogtot : Real.log (∑ i ∈ s, Real.exp (-(t * y i)))
      ≤ -(t * mu) + Real.log p + q * E / p := by linarith
  have hinv : (0 : ℝ) ≤ 1 / t := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlogtot hinv
  have hrewrite : (1 / t) * (-(t * mu) + Real.log p + q * E / p)
      = -mu + Real.log p / t + q * E / (p * t) := by
    field_simp
  rw [hrewrite] at hmul
  simp only [softMin]
  have : -(1 / t) * Real.log (∑ i ∈ s, Real.exp (-(t * y i)))
      = -((1 / t) * Real.log (∑ i ∈ s, Real.exp (-(t * y i)))) := by ring
  rw [this]
  linarith
