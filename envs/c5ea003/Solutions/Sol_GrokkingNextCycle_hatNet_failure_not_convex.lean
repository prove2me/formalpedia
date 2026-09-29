-- Prove2me | solution 1 for GrokkingNextCycle.hatNet_failure_not_convex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-20T13:40:11.187531+00:00
-- url     : https://prove2.me/submissions/d9e9d6a9-0d2c-4fd5-b681-a0bf993ba774

-- Sol generated from MachineLearning/GrokkingDelayedTransition/NextCycle.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_NextCycle
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_VectorMargin
import Theorems.Thm_GrokkingNextCycle_hatNet_failure_set

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
theorem solution: ¬ Convex ℝ {t : ℝ | hatNet t ≤ 0} := by
  intro hconv
  have h0 : (0 : ℝ) ∈ {t : ℝ | hatNet t ≤ 0} := by
    rw [hatNet_failure_set]; left; norm_num
  have h2 : (2 : ℝ) ∈ {t : ℝ | hatNet t ≤ 0} := by
    rw [hatNet_failure_set]; right; norm_num
  have hmid := hconv h0 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  have h1 : (1 : ℝ) ∈ {t : ℝ | hatNet t ≤ 0} := by
    simpa using hmid
  rw [hatNet_failure_set] at h1
  rcases h1 with h | h <;> norm_num at h
