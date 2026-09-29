-- Prove2me | solution 1 for RLHF.tiltMean_drift_constant_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:25:08.327417+00:00
-- url     : https://prove2.me/submissions/aa1bd3c4-9667-4217-ba60-d9aeb04a8c7d

-- Sol generated from NumberTheory/RLHFVarianceSharpness.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFVarianceCurvature
import Definitions.Def_NumberTheory_RLHFVarianceSharpness
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_hasDerivAt_tiltMean

/-!
# Sharpness of the alignment speed limit, and curvature of the Euler factors

This file closes two of the three next-cycle sub-conjectures recorded in
`FUTURE_DIRECTIONS.md` after the curvature identity
`RLHF.deriv2_logExpMoment_eq_tiltVar` was proved.

**Sub-conjecture 1 (sharpness of the speed limit).**  `RLHF.tiltVar_le_range_sq` caps the
reward variance of a model confined to `[m, M]` by `(M − m)²/4`, and
`RLHF.tiltMean_drift_le` turns that into a temperature-uniform speed limit for alignment.
Here we show that the constant `1/4` cannot be improved and describe exactly when it is
attained:

* `RLHF.tiltVar_shift` — the variance of the tilted policy computed around an arbitrary
  centre.
* `RLHF.tiltVar_eq_range_sq_iff` — **the equality analysis**: the Popoviciu ceiling is
  attained at a temperature `t` if and only if the reward model is two-valued, taking only
  the extreme values `m` and `M`, *and* the tilted policy splits its mass evenly between the
  two levels (equivalently `𝔼_{π_t}[r] = (m+M)/2`).
* `RLHF.twoAtom_tiltVar`, `RLHF.twoAtom_tiltVar_zero` — the extremal model: the two-atom
  reward `r ∈ {0,1}` with balanced reference has `Var_{π_t}(r) = e^t/(1+e^t)²`, equal to
  `1/4` at `t = 0`.
* `RLHF.popoviciu_constant_sharp` and `RLHF.tiltMean_drift_constant_sharp` — consequently no
  constant below `1/4` can appear either in the variance ceiling or in the drift bound; the
  second statement is a genuine derivative argument (the slope of the logistic alignment
  curve at the origin).

**Sub-conjecture 2 (curvature of the Euler factors).**  The local zeta factor
`localZeta s p A = ∑_{k ≤ A} p^{-ks}` is the RLHF partition function of the reward
`k ↦ −k log p` on the exponent space `{0, …, A}` with uniform reference:

* `RLHF.expMoment_zero_geomReward` — the identification.
* `RLHF.convexOn_logLocalZeta`, `RLHF.strictConvexOn_logLocalZeta` — each Euler factor is
  log-convex in the exponent, strictly so for `p ≥ 2` and `A ≥ 1`.
* `RLHF.localZeta_curvature_eq_variance` — `d²/ds² log localZeta = Var(k log p)` under the
  truncated geometric law on exponents.
* `RLHF.zetaSum_curvature_additive` — **additive curvature decomposition**: the curvature of
  the truncated Euler product is the sum of the per-prime curvatures.  Alignment "difficulty"
  is a sum of independent local contributions.
-/

open RLHF

open Finset Filter Topology

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Variance around an arbitrary centre -/


/-! ## 2. Equality analysis for the Popoviciu ceiling -/


/-! ## 3. The extremal two-atom model -/



theorem twoRef_pos : ∀ b : Bool, 0 < twoRef b := by
  intro b; unfold twoRef; norm_num



theorem twoAtom_expMoment_zero (t : ℝ) :
    expMoment 0 twoReward twoRef t = (Real.exp t + 1) / 2 := by
  simp [expMoment, twoReward, twoRef]
  ring

theorem twoAtom_expMoment_one (t : ℝ) :
    expMoment 1 twoReward twoRef t = Real.exp t / 2 := by
  simp [expMoment, twoReward, twoRef]
  ring

theorem twoAtom_expMoment_two (t : ℝ) :
    expMoment 2 twoReward twoRef t = Real.exp t / 2 := by
  simp [expMoment, twoReward, twoRef]
  ring

/-- The aligned expected reward of the two-atom model is the logistic curve. -/
theorem twoAtom_tiltMean (t : ℝ) :
    tiltMean twoReward twoRef t = Real.exp t / (Real.exp t + 1) := by
  have hpos : (0 : ℝ) < Real.exp t + 1 := by positivity
  unfold tiltMean
  rw [twoAtom_expMoment_one, twoAtom_expMoment_zero]
  field_simp

/-- The reward variance of the two-atom model, `e^t/(1+e^t)²`. -/
theorem twoAtom_tiltVar (t : ℝ) :
    tiltVar twoReward twoRef t = Real.exp t / (Real.exp t + 1) ^ 2 := by
  have hpos : (0 : ℝ) < Real.exp t + 1 := by positivity
  unfold tiltVar
  rw [twoAtom_expMoment_two, twoAtom_expMoment_zero, twoAtom_tiltMean]
  field_simp
  ring

/-- At the balanced temperature the two-atom model attains the Popoviciu ceiling. -/
theorem twoAtom_tiltVar_zero : tiltVar twoReward twoRef 0 = 1 / 4 := by
  rw [twoAtom_tiltVar]
  norm_num


theorem twoAtom_hasDerivAt_zero : HasDerivAt (tiltMean twoReward twoRef) (1 / 4) 0 := by
  have h := hasDerivAt_tiltMean (r := twoReward) twoRef_pos 0
  rwa [twoAtom_tiltVar_zero] at h


/-! ## 4. Curvature of the Euler factors -/











open RLHF in
theorem solution{C : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → tiltMean twoReward twoRef t - tiltMean twoReward twoRef 0 ≤ t * C) :
    1 / 4 ≤ C := by
  have hd := twoAtom_hasDerivAt_zero
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  have h2 : Tendsto (slope (tiltMean twoReward twoRef) 0) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 4)) :=
    hd.mono_left hsub
  refine le_of_tendsto h2 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : (0 : ℝ) < t := ht
  have hbound := h t htpos.le
  rw [slope_def_field, sub_zero, div_le_iff₀ htpos]
  linarith [hbound]
