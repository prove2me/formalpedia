-- Prove2me | Theorems.Thm_GrokkingTraining_gd_delay_lower_bound
-- name    : GrokkingTraining.gd_delay_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:33:43.555911+00:00
-- url     : https://prove2.me/theorems/f1316084-3ad5-4542-afaf-2e48cf5da5d7
-- title:
--   Logarithmic delay for gradient descent.
-- statement:
--   **Logarithmic delay for gradient descent.**  If the iterate has crossed the
--   threshold `θ` at step `k`, then `k` is at least `log(gap ratio) / log(1-ηλ)`;
--   as `θ` approaches the regularized optimum `s/λ` this bound diverges.
--
--   ```lean
--   theorem GrokkingTraining.gd_delay_lower_bound(eta lam s w0 theta : ℝ) (hlam : 0 < lam)
--       (heta : 0 < eta) (hrho : eta * lam < 1) (hw0 : w0 < theta) (hth : theta < s / lam)
--       (k : ℕ) (hk : theta < gdSeq eta lam s w0 k) :
--       Real.log ((s / lam - theta) / (s / lam - w0)) / Real.log (1 - eta * lam) < k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean#L312

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





/-! ### The weight decay as bifurcation parameter -/





/-! ### Divergence of the delay at criticality -/



/-! ### Discrete weight-decayed gradient descent -/

theorem GrokkingTraining.gd_delay_lower_bound(eta lam s w0 theta : ℝ) (hlam : 0 < lam)
    (heta : 0 < eta) (hrho : eta * lam < 1) (hw0 : w0 < theta) (hth : theta < s / lam)
    (k : ℕ) (hk : theta < gdSeq eta lam s w0 k) :
    Real.log ((s / lam - theta) / (s / lam - w0)) / Real.log (1 - eta * lam) < k := by sorry
