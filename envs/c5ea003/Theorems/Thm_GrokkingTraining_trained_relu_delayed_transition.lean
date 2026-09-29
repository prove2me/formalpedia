-- Prove2me | Theorems.Thm_GrokkingTraining_trained_relu_delayed_transition
-- name    : GrokkingTraining.trained_relu_delayed_transition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:33:53.00698+00:00
-- url     : https://prove2.me/theorems/8d4bd5b5-0446-4456-8705-59805dc75a41
-- title:
--   Delayed transition with a derived delay.
-- statement:
--   **Delayed transition with a derived delay.**  The ReLU unit driven by the
--   weight-decayed gradient flow is exactly silent up to `crossTime` and strictly
--   active afterwards.  This is the catalog's `delayed_generalization`, but the
--   delay is now produced by the training dynamics rather than assumed.
--
--   ```lean
--   theorem GrokkingTraining.trained_relu_delayed_transition(lam s w0 theta : ℝ) (hlam : 0 < lam)
--       (hw0 : w0 < theta) (hth : theta < s / lam) :
--       (∀ t ≤ crossTime lam s w0 theta, relu (wdFlow lam s w0 t - theta) = 0) ∧
--         (∀ t, crossTime lam s w0 theta < t → 0 < relu (wdFlow lam s w0 t - theta)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean#L159

-- Thm stub generated from MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean
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

theorem GrokkingTraining.trained_relu_delayed_transition(lam s w0 theta : ℝ) (hlam : 0 < lam)
    (hw0 : w0 < theta) (hth : theta < s / lam) :
    (∀ t ≤ crossTime lam s w0 theta, relu (wdFlow lam s w0 t - theta) = 0) ∧
      (∀ t, crossTime lam s w0 theta < t → 0 < relu (wdFlow lam s w0 t - theta)) := by sorry
