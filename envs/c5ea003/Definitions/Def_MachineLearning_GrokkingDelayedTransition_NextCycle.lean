-- Prove2me | Definitions.Def_MachineLearning_GrokkingDelayedTransition_NextCycle
-- name    : MachineLearning_GrokkingDelayedTransition_NextCycle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T17:06:28.98151+00:00
-- url     : https://prove2.me/theorems/811841cc-87e4-4dea-9f6b-1a4e8070d281
-- title:
--   Aether Catalog definitions — MachineLearning_GrokkingDelayedTransition_NextCycle
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.GrokkingDelayedTransition.NextCycle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/GrokkingDelayedTransition/NextCycle.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_GrokkingDelayedTransition_GradientFlowThreshold
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

namespace GrokkingNextCycle

open Filter Topology Set

/-! ### (N1) The delay diverges, as a limit along `𝓝[<] λ_c` -/


/-! ### (N2) An exact delay formula, and the `1/m` width law -/

open GrokkingVector




/-- The symmetric width-`m` network: `m` identical hidden units with weight `g`,
zero hidden bias and output weight `A`, output bias `c`, probed along the ramp
`t ↦ t`. -/
noncomputable def symNet (m : ℕ) (A g c : ℝ) : ℝ → ℝ :=
  netRamp (fun _ : Fin m => fun _ : Fin 1 => g) (fun _ => 0) (fun _ => A) c
    (fun _ : Fin 1 => 1)



/-- The delay of the symmetric width-`m` network. -/
noncomputable def symDelay (m : ℕ) (A g c : ℝ) : ℝ := -c / ((m : ℝ) * (A * g))




/-! ### (N3) A sign-indefinite network that groks twice -/

/-- Hidden weights of the "hat" network: three units, one input dimension. -/
def hatW : Fin 3 → Fin 1 → ℝ := fun _ _ => 1

/-- Hidden biases `0, -1, -2` of the hat network. -/
def hatB : Fin 3 → ℝ := ![0, -1, -2]

/-- **Sign-indefinite** output weights `1, -2, 1` of the hat network. -/
def hatA : Fin 3 → ℝ := ![1, -2, 1]


/-- The hat network: output bias `-1/2`, probed along the ramp `t ↦ t`. -/
noncomputable def hatNet : ℝ → ℝ :=
  netRamp hatW hatB hatA (-1 / 2) (fun _ : Fin 1 => 1)





/-! ### Sharpness of the robustness displacement bound -/

/-- A trajectory with exact linear growth `κ(t - τ)` after its threshold `τ`. -/
noncomputable def linTraj (kappa tau : ℝ) : ℝ → ℝ := fun t => kappa * (t - tau)

/-- The constant `-ε` perturbation of `linTraj`. -/
noncomputable def linTrajPerturbed (kappa tau eps : ℝ) : ℝ → ℝ :=
  fun t => kappa * (t - tau) - eps



end GrokkingNextCycle


