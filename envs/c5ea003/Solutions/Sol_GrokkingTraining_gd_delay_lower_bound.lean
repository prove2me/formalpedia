-- Prove2me | solution 1 for GrokkingTraining.gd_delay_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:54:26.238871+00:00
-- url     : https://prove2.me/submissions/3059d4c5-43c8-4f41-9be2-e60c69998e6b

-- Sol generated from MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold

/-!
# Deriving the grokking delay from weight-decayed training dynamics

In `Catalog/MachineLearning/GrokkingPhaseTransition.lean` the delay of the
two-layer ReLU network is *prescribed*: the bias is `-delay` by fiat.  This file
carries out Future Direction 2 (training dynamics) and part of Direction 6
(connection theorem): the delay is *derived* as the crossing time of a
weight-decayed gradient flow / gradient descent, and the bifurcation parameter of
the saddle-node normal form becomes an explicit function of the weight-decay
strength.

Main results.

* `wdFlow_hasDerivAt`, `wdFlow_isGradientFlow`, `wdFlow_init`: the explicit
  trajectory `w(t) = s/λ + (w₀ - s/λ) e^{-λ t}` is *the* gradient flow of the
  weight-decayed loss `λ w²/2 - s w`.
* `wdFlow_strictMono`, `wdFlow_lt_limit`: the trained weight increases strictly
  towards, but never reaches, the regularized optimum `s/λ`.
* `wdFlow_gt_threshold_iff`: the trajectory exceeds a fixed activation threshold
  `θ` *exactly* after the explicit time `crossTime = λ⁻¹ log((s/λ-w₀)/(s/λ-θ))`.
* `trained_relu_delayed_transition`: consequently the trained ReLU unit outputs
  exactly `0` up to `crossTime` and is strictly positive afterwards — the
  catalog's delayed transition, now with a *derived* delay.
* `crossing_exists_iff_subcritical_decay`: the threshold is crossed at all iff
  the weight decay is subcritical, `λ < λ_c := s/θ`, i.e. iff the saddle-node
  parameter `bifParam := s/λ - θ` is positive.  This is the promised connection
  between the optimization/regularization parameter and the normal form.
* `crossTime_diverges_at_criticality`: the delay is unbounded as the weight decay
  approaches its critical value — the grokking time diverges at the bifurcation.
* `gdSeq_closed_form`, `gd_delay_lower_bound`: the discrete weight-decayed
  gradient-descent iteration has the analogous closed form, and the number of
  steps before the threshold is crossed grows like `log(1/gap)`.
-/

open GrokkingTraining

open Real

/-! ### The weight-decayed loss and its gradient flow -/







/-! ### Monotone approach to the regularized optimum -/


/-! ### The crossing time: an explicit, derived delay -/





/-! ### The weight decay as bifurcation parameter -/





/-! ### Divergence of the delay at criticality -/



/-! ### Discrete weight-decayed gradient descent -/


/-- Closed form of the weight-decayed gradient-descent iteration. -/
theorem gdSeq_closed_form (eta lam s w0 : ℝ) (hlam : lam ≠ 0) (k : ℕ) :
    gdSeq eta lam s w0 k = s / lam + (w0 - s / lam) * (1 - eta * lam) ^ k := by
  induction k with
  | zero => simp [gdSeq]
  | succ k ih =>
      simp only [gdSeq, ih, pow_succ]
      field_simp
      ring



open GrokkingTraining in
theorem solution(eta lam s w0 theta : ℝ) (hlam : 0 < lam)
    (heta : 0 < eta) (hrho : eta * lam < 1) (hw0 : w0 < theta) (hth : theta < s / lam)
    (k : ℕ) (hk : theta < gdSeq eta lam s w0 k) :
    Real.log ((s / lam - theta) / (s / lam - w0)) / Real.log (1 - eta * lam) < k := by
  have hA : 0 < s / lam - w0 := by linarith
  have hB : 0 < s / lam - theta := by linarith
  have hrhopos : 0 < 1 - eta * lam := by nlinarith
  have hrholt : 1 - eta * lam < 1 := by nlinarith
  rw [gdSeq_closed_form eta lam s w0 (ne_of_gt hlam) k] at hk
  have hpow : (1 - eta * lam) ^ k < (s / lam - theta) / (s / lam - w0) := by
    rw [lt_div_iff₀ hA]
    nlinarith
  have hlogrho : Real.log (1 - eta * lam) < 0 := Real.log_neg hrhopos hrholt
  have hlogpow : (k : ℝ) * Real.log (1 - eta * lam)
      < Real.log ((s / lam - theta) / (s / lam - w0)) := by
    have h1 : Real.log ((1 - eta * lam) ^ k) < Real.log ((s / lam - theta) / (s / lam - w0)) :=
      Real.log_lt_log (by positivity) hpow
    rwa [Real.log_pow] at h1
  rw [div_lt_iff_of_neg hlogrho]
  linarith
