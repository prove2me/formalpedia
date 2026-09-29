-- Prove2me | solution 1 for GrokkingTraining.trained_relu_delayed_transition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:54:26.702553+00:00
-- url     : https://prove2.me/submissions/d69b22b4-b36a-4289-a7a5-b8d614371eae

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





/-! ### Divergence of the delay at criticality -/



/-! ### Discrete weight-decayed gradient descent -/





open GrokkingTraining in
theorem solution(lam s w0 theta : ℝ) (hlam : 0 < lam)
    (hw0 : w0 < theta) (hth : theta < s / lam) :
    (∀ t ≤ crossTime lam s w0 theta, relu (wdFlow lam s w0 t - theta) = 0) ∧
      (∀ t, crossTime lam s w0 theta < t → 0 < relu (wdFlow lam s w0 t - theta)) := by
  constructor
  · intro t ht
    have hle : wdFlow lam s w0 t ≤ theta := by
      by_contra hcon
      push_neg at hcon
      exact absurd ((wdFlow_gt_threshold_iff lam s w0 theta t hlam hw0 hth).mp hcon)
        (not_lt.mpr ht)
    simp only [relu]
    exact max_eq_right (by linarith)
  · intro t ht
    have hgt := (wdFlow_gt_threshold_iff lam s w0 theta t hlam hw0 hth).mpr ht
    simp only [relu]
    exact lt_max_of_lt_left (by linarith)
