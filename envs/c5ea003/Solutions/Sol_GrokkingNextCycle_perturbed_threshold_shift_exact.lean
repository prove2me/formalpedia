-- Prove2me | solution 1 for GrokkingNextCycle.perturbed_threshold_shift_exact
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-20T13:40:11.716081+00:00
-- url     : https://prove2.me/submissions/93d142eb-e42c-427f-8163-f0b04f0ffa82

-- Sol generated from MachineLearning/GrokkingDelayedTransition/NextCycle.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_NextCycle
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_VectorMargin

/-!
# Closing the three next-cycle sub-conjectures of the grokking thread

`FUTURE_DIRECTIONS.md` of the previous cycle listed three concrete sub-conjectures
(N1)–(N3), and a sharpness half for Conjecture 4.  This file resolves all of
them, building directly on the definitions of
`GrokkingDelayedTransition/GradientFlowThreshold.lean` and
`GrokkingDelayedTransition/VectorMargin.lean`.

* **(N1) Filter-level divergence of the delay.**  `crossTime_tendsto_atTop`:
  the crossing time of the weight-decayed gradient flow tends to `+∞` as the
  weight decay increases to its critical value `λ_c = s/θ`.  This upgrades the
  purely existential `crossTime_diverges_at_criticality` to a genuine limit
  statement along the filter `𝓝[<] λ_c`.

* **(N2) An exact `1/m` width law.**  `zeroBias_sharp_threshold`: for a network
  with vanishing hidden biases the *sandwich* `delay_scaling_sandwich` collapses
  to an **equality**, the sharp delay being exactly `|c| / S` with
  `S = ∑ⱼ aⱼ gⱼ` the total signal.  Specialized to a symmetric width-`m`
  network (`symNet_sharp_threshold`) this gives `τ(m) = |c| / (m a g)`, hence
  the exact width law `m · τ(m) = |c|/(a g)` (`symNet_delay_width_law`) and
  `τ(m) → 0` (`symNet_delay_tendsto_zero`).

* **(N3) Grokking can happen twice.**  `hatNet_failure_set` computes the failure
  set of an explicit *sign-indefinite* width-three network to be exactly
  `(-∞, 1/2] ∪ [3/2, ∞)`, and `hatNet_failure_not_convex` shows it is not
  convex.  So the nonnegativity of the output weights in `netRamp_convexOn` /
  `failure_set_convex` cannot be dropped: with signed output weights a network
  can grok, un-grok and re-grok.

* **Sharpness of the robustness bound.**  `perturbed_threshold_shift_exact`:
  the displacement `ε/κ` of `perturbed_delayed_transition` is attained by the
  constant perturbation `-ε`, so that bound is sharp.
-/

open GrokkingNextCycle

open Filter Topology Set

/-! ### (N1) The delay diverges, as a limit along `𝓝[<] λ_c` -/


/-! ### (N2) An exact delay formula, and the `1/m` width law -/

open GrokkingVector











/-! ### (N3) A sign-indefinite network that groks twice -/










/-! ### Sharpness of the robustness displacement bound -/






open GrokkingNextCycle in
theorem solution(kappa tau eps : ℝ) (hkappa : 0 < kappa)
    (heps : 0 ≤ eps) :
    (∀ t, |linTrajPerturbed kappa tau eps t - linTraj kappa tau t| ≤ eps) ∧
      (∀ t ≤ tau, linTraj kappa tau t ≤ 0) ∧
      (∀ t, tau < t → kappa * (t - tau) ≤ linTraj kappa tau t) ∧
      (∀ t ≤ tau + eps / kappa, linTrajPerturbed kappa tau eps t ≤ 0) ∧
      (∀ t, tau + eps / kappa < t → 0 < linTrajPerturbed kappa tau eps t) := by
  refine ⟨fun t => ?_, fun t ht => ?_, fun t _ => le_rfl, fun t ht => ?_, fun t ht => ?_⟩
  · simp only [linTrajPerturbed, linTraj]
    rw [show kappa * (t - tau) - eps - kappa * (t - tau) = -eps by ring, abs_neg,
      abs_of_nonneg heps]
  · simp only [linTraj]
    nlinarith
  · simp only [linTrajPerturbed]
    have h : t - tau ≤ eps / kappa := by linarith
    have := (le_div_iff₀ hkappa).mp h
    nlinarith
  · simp only [linTrajPerturbed]
    have h : eps / kappa < t - tau := by linarith
    have := (div_lt_iff₀ hkappa).mp h
    nlinarith
