-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.mode_gradFlow_le_four_ridge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:44:01.316279+00:00
-- url     : https://prove2.me/submissions/ed3c9901-2a93-40ea-94e9-275d18c73aae

-- Sol generated from MachineLearning/NoiseFloor/EarlyStopping.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EarlyStopping
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
/-
# The Noise-Floor Principle, Part VII: early stopping versus ridge

Round-6 hypothesis closure, Phase A, cycle 4.

Gradient flow on a quadratic loss with data covariance spectrum `mu`, stopped at
time `tau`, is the spectral filter

  `gradFlowFilter mu tau i = 1 - exp (- mu i * tau)`,

the continuous-time idealisation of early stopping.  Folklore says "early
stopping is ridge with `lam = 1/tau`".  We make the folklore precise **and show
it is one-sided**:

* `gradFlow_le_four_mul_ridge` — early stopping at time `tau` is never worse
  than four times the matched ridge `lam = 1/tau`, for every spectrum, every
  signal and every noise level;
* `ridge_can_be_arbitrarily_worse` — the converse fails badly: on an explicit
  one-mode problem the matched ridge costs more than `100×` early stopping.

Both filters obey the Part II floor (`gradFlow_ge_noiseFloor`), so the
comparison is a statement about *how* the two families approach the same
irreducible limit: the exponential filter kills the bias of well-conditioned
modes at an exponential rate, while ridge only kills it polynomially.

## Main results

* `one_sub_exp_le_two_mul`   — `1 - e^{-u} ≤ 2u/(1+u)` (uniform in `u ≥ 0`)
* `exp_neg_le_one_div`       — `e^{-u} ≤ 1/(1+u)`
* `gradFlow_le_four_mul_ridge`, `gradFlow_ge_noiseFloor`
* `ridge_can_be_arbitrarily_worse`
-/

open Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]



/-- `e^{-u} ≤ 1/(1+u)` for `u ≥ 0`: the exponential filter has smaller bias than
the matched ridge filter. -/
lemma exp_neg_le_one_div {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ≤ 1 / (1 + u) := by
  have h1 : 0 < 1 + u := by linarith
  have h2 : 1 + u ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    linarith
  rw [Real.exp_neg, one_div]
  gcongr

/-- `1 - e^{-u} ≤ 2u/(1+u)` for `u ≥ 0`: the exponential filter has at most twice
the shrinkage weight of the matched ridge filter. -/
lemma one_sub_exp_le_two_mul {u : ℝ} (hu : 0 ≤ u) :
    1 - Real.exp (-u) ≤ 2 * u / (1 + u) := by
  have h1 : 0 < 1 + u := by linarith
  rcases le_total u 1 with h | h
  · have hlin : 1 - u ≤ Real.exp (-u) := by
      have := Real.add_one_le_exp (-u)
      linarith
    rw [le_div_iff₀ h1]
    nlinarith
  · have hpos : 0 < Real.exp (-u) := Real.exp_pos _
    rw [le_div_iff₀ h1]
    nlinarith

/-- Nonnegativity of the exponential filter weight. -/
lemma one_sub_exp_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ 1 - Real.exp (-u) := by
  have : Real.exp (-u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  linarith




variable {a mu : ι → ℝ} {b tau : ℝ}










open Catalog.MachineLearning.NoiseFloor in
theorem solution{x b u : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) (hu : 0 ≤ u) :
    x * (1 - (1 - Real.exp (-u))) ^ 2 + b * (1 - Real.exp (-u)) ^ 2
      ≤ 4 * (x * (1 - u / (1 + u)) ^ 2 + b * (u / (1 + u)) ^ 2) := by
  have h1 : 0 < 1 + u := by linarith
  have hbias : (1 : ℝ) - u / (1 + u) = 1 / (1 + u) := by
    field_simp
    ring
  have he : Real.exp (-u) ≤ 1 / (1 + u) := exp_neg_le_one_div hu
  have he0 : 0 < Real.exp (-u) := Real.exp_pos _
  have hsq1 : (Real.exp (-u)) ^ 2 ≤ (1 / (1 + u)) ^ 2 := by nlinarith [he0.le]
  have ht : 1 - Real.exp (-u) ≤ 2 * (u / (1 + u)) := by
    have := one_sub_exp_le_two_mul hu
    rw [mul_div_assoc] at this
    exact this
  have ht0 : 0 ≤ 1 - Real.exp (-u) := one_sub_exp_nonneg hu
  have hsq2 : (1 - Real.exp (-u)) ^ 2 ≤ 4 * (u / (1 + u)) ^ 2 := by nlinarith
  have e1 : x * (1 - (1 - Real.exp (-u))) ^ 2 = x * (Real.exp (-u)) ^ 2 := by ring_nf
  rw [e1, hbias]
  nlinarith [mul_le_mul_of_nonneg_left hsq1 hx, mul_le_mul_of_nonneg_left hsq2 hb,
    sq_nonneg (1 / (1 + u)), mul_nonneg hx (sq_nonneg (1 / (1 + u)))]
