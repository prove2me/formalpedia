-- Prove2me | solution 1 for GrokkingTraining.crossing_exists_iff_subcritical_decay
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:54:25.695403+00:00
-- url     : https://prove2.me/submissions/4c05c5c6-35f1-45c0-9222-5cdff56a0ba2

-- Sol generated from MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
import Theorems.Thm_GrokkingTraining_wdFlow_gt_threshold_iff

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



/-- The bifurcation parameter is positive exactly below the critical weight
decay. -/
theorem bifParam_pos_iff (lam s theta : ℝ) (hlam : 0 < lam) (hth : 0 < theta) :
    0 < bifParam lam s theta ↔ lam < criticalDecay s theta := by
  simp only [bifParam, criticalDecay, sub_pos]
  rw [lt_div_iff₀ hlam, lt_div_iff₀ hth]
  constructor <;> intro h <;> nlinarith


/-! ### Divergence of the delay at criticality -/



/-! ### Discrete weight-decayed gradient descent -/





open GrokkingTraining in
theorem solution(lam s w0 theta : ℝ) (hlam : 0 < lam)
    (hth : 0 < theta) (hw0 : w0 < theta) :
    (∃ t : ℝ, 0 ≤ t ∧ theta < wdFlow lam s w0 t) ↔ lam < criticalDecay s theta := by
  rw [← bifParam_pos_iff lam s theta hlam hth]
  simp only [bifParam, sub_pos]
  constructor
  · rintro ⟨t, ht0, ht⟩
    by_contra hcon
    push_neg at hcon
    have hE0 : 0 < Real.exp (-(lam * t)) := Real.exp_pos _
    have hE1 : Real.exp (-(lam * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    simp only [wdFlow] at ht
    nlinarith [mul_nonneg (sub_nonneg.mpr hE1) (sub_nonneg.mpr hcon),
      mul_pos hE0 (sub_pos.mpr hw0)]
  · intro h
    refine ⟨max 0 (crossTime lam s w0 theta) + 1, by positivity, ?_⟩
    refine (wdFlow_gt_threshold_iff lam s w0 theta _ hlam hw0 h).mpr ?_
    have := le_max_right 0 (crossTime lam s w0 theta)
    linarith
