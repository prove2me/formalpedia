-- Prove2me | solution 1 for RLHF.localZeta_curvature_eq_variance
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:15:18.017374+00:00
-- url     : https://prove2.me/submissions/69da9864-a7a0-4720-882c-14c6446d766a

-- Sol generated from NumberTheory/RLHFVarianceSharpness.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFVarianceCurvature
import Definitions.Def_NumberTheory_RLHFVarianceSharpness
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_deriv_tiltMean
import Theorems.Thm_RLHF_expMoment_zero_geomReward
import Theorems.Thm_RLHF_hasDerivAt_logExpMoment
import Theorems.Thm_RLHF_localZeta_pos
import Theorems.Thm_RLHF_unifWeight_pos

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















/-! ## 4. Curvature of the Euler factors -/



theorem logExpMoment_geomReward {p A : ℕ} (hp : 0 < p) :
    (fun s => Real.log (expMoment 0 (geomReward p A) (unifWeight (A + 1)) s))
      = fun s => Real.log (localZeta s p A) + (-Real.log ((A : ℝ) + 1)) := by
  funext s
  have hA : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hL : (0 : ℝ) < localZeta s p A := localZeta_pos hp
  rw [expMoment_zero_geomReward hp, Real.log_mul (by positivity) (ne_of_gt hL), Real.log_inv]
  ring


theorem hasDerivAt_logLocalZeta {p A : ℕ} (hp : 0 < p) (s : ℝ) :
    HasDerivAt (fun s => Real.log (localZeta s p A))
      (tiltMean (geomReward p A) (unifWeight (A + 1)) s) s := by
  have h := hasDerivAt_logExpMoment (r := geomReward p A)
    (unifWeight_pos (Nat.succ_pos A)) s
  rw [logExpMoment_geomReward hp] at h
  simpa using h.sub_const (-Real.log ((A : ℝ) + 1))






open RLHF in
theorem solution{p A : ℕ} (hp : 0 < p) :
    deriv^[2] (fun s => Real.log (localZeta s p A))
      = tiltVar (geomReward p A) (unifWeight (A + 1)) := by
  have hderiv1 : deriv (fun s => Real.log (localZeta s p A))
      = tiltMean (geomReward p A) (unifWeight (A + 1)) := by
    funext s
    exact (hasDerivAt_logLocalZeta hp s).deriv
  have hderiv2 : deriv (tiltMean (geomReward p A) (unifWeight (A + 1)))
      = tiltVar (geomReward p A) (unifWeight (A + 1)) :=
    deriv_tiltMean (unifWeight_pos (Nat.succ_pos A))
  have h2 : deriv^[2] (fun s => Real.log (localZeta s p A))
      = deriv (deriv (fun s => Real.log (localZeta s p A))) := by
    simp [Function.iterate_succ]
  rw [h2, hderiv1, hderiv2]
