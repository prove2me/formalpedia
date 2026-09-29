-- Prove2me | solution 1 for GrokkingTraining.wdFlow_gt_threshold_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:52:45.147349+00:00
-- url     : https://prove2.me/submissions/f30ddc55-1b15-4680-b659-c8ffe5c3bac9

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





open GrokkingTraining in
theorem solution(lam s w0 theta t : ℝ) (hlam : 0 < lam)
    (hw0 : w0 < theta) (hth : theta < s / lam) :
    theta < wdFlow lam s w0 t ↔ crossTime lam s w0 theta < t := by
  have hA : 0 < s / lam - w0 := by linarith
  have hB : 0 < s / lam - theta := by linarith
  have hlog : Real.log ((s / lam - theta) / (s / lam - w0))
      = -Real.log ((s / lam - w0) / (s / lam - theta)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  constructor
  · intro h
    simp only [wdFlow] at h
    have hexp : Real.exp (-(lam * t)) < (s / lam - theta) / (s / lam - w0) := by
      rw [lt_div_iff₀ hA]
      nlinarith
    have hpos : 0 < (s / lam - theta) / (s / lam - w0) := div_pos hB hA
    have hlt : -(lam * t) < Real.log ((s / lam - theta) / (s / lam - w0)) :=
      (Real.lt_log_iff_exp_lt hpos).mpr hexp
    rw [hlog] at hlt
    simp only [crossTime]
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hlam]
    nlinarith
  · intro h
    simp only [crossTime] at h
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hlam] at h
    have hlt : -(lam * t) < Real.log ((s / lam - theta) / (s / lam - w0)) := by
      rw [hlog]; nlinarith
    have hpos : 0 < (s / lam - theta) / (s / lam - w0) := div_pos hB hA
    have hexp : Real.exp (-(lam * t)) < (s / lam - theta) / (s / lam - w0) := by
      have := Real.exp_lt_exp.mpr hlt
      rwa [Real.exp_log hpos] at this
    rw [lt_div_iff₀ hA] at hexp
    simp only [wdFlow]
    nlinarith
