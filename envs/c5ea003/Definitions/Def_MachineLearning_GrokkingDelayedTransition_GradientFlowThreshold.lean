-- Prove2me | Definitions.Def_MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
-- name    : MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:42:59.163982+00:00
-- url     : https://prove2.me/theorems/0f7fbebe-b4aa-40e0-82d0-6be591ffaa3a
-- title:
--   Aether Catalog definitions — MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.GrokkingDelayedTransition.GradientFlowThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/GrokkingDelayedTransition/GradientFlowThreshold.lean by skeleton subtraction
import Mathlib

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

namespace GrokkingTraining

open Real

/-! ### The weight-decayed loss and its gradient flow -/

/-- Weight-decayed (ridge) training loss for a single scalar weight: the data
term pushes the weight up with force `s`, the decay term pulls it back. -/
noncomputable def wdLoss (lam s w : ℝ) : ℝ := lam / 2 * w ^ 2 - s * w

/-- The explicit solution of the weight-decayed gradient flow with initial
weight `w₀`. -/
noncomputable def wdFlow (lam s w0 t : ℝ) : ℝ :=
  s / lam + (w0 - s / lam) * Real.exp (-(lam * t))





/-! ### Monotone approach to the regularized optimum -/


/-! ### The crossing time: an explicit, derived delay -/

/-- The time at which the weight-decayed gradient flow reaches the activation
threshold `θ`. -/
noncomputable def crossTime (lam s w0 theta : ℝ) : ℝ :=
  (1 / lam) * Real.log ((s / lam - w0) / (s / lam - theta))


/-- The rectifier. -/
noncomputable def relu (x : ℝ) : ℝ := max x 0


/-! ### The weight decay as bifurcation parameter -/

/-- The saddle-node bifurcation parameter attached to a weight-decay strength:
the signed gap between the regularized optimum and the activation threshold. -/
noncomputable def bifParam (lam s theta : ℝ) : ℝ := s / lam - theta

/-- The critical weight decay: `λ_c = s/θ`. -/
noncomputable def criticalDecay (s theta : ℝ) : ℝ := s / theta



/-! ### Divergence of the delay at criticality -/



/-! ### Discrete weight-decayed gradient descent -/

/-- Weight-decayed gradient descent with learning rate `η`. -/
noncomputable def gdSeq (eta lam s w0 : ℝ) : ℕ → ℝ
  | 0 => w0
  | k + 1 => gdSeq eta lam s w0 k - eta * (lam * gdSeq eta lam s w0 k - s)



end GrokkingTraining


