-- Prove2me | Theorems.Thm_GrokkingNextCycle_symNet_sharp_threshold
-- name    : GrokkingNextCycle.symNet_sharp_threshold
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:48:13.489355+00:00
-- url     : https://prove2.me/theorems/411b8734-e505-41bf-9700-f9edde718874
-- title:
--   Sharp delay of the symmetric width-`m` network.
-- statement:
--   **Sharp delay of the symmetric width-`m` network.**
--
--   ```lean
--   theorem GrokkingNextCycle.symNet_sharp_threshold(m : ℕ) (A g c : ℝ) (hm : 0 < m) (hA : 0 < A)
--       (hg : 0 < g) (hc : c < 0) :
--       (∀ t ≤ symDelay m A g c, symNet m A g c t ≤ 0) ∧
--         (∀ t, symDelay m A g c < t → 0 < symNet m A g c t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingDelayedTransition/NextCycle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingDelayedTransition/NextCycle.lean#L206

-- Thm stub generated from MachineLearning/GrokkingDelayedTransition/NextCycle.lean
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

-- open removed: section is not a namespace

theorem GrokkingNextCycle.symNet_sharp_threshold(m : ℕ) (A g c : ℝ) (hm : 0 < m) (hA : 0 < A)
    (hg : 0 < g) (hc : c < 0) :
    (∀ t ≤ symDelay m A g c, symNet m A g c t ≤ 0) ∧
      (∀ t, symDelay m A g c < t → 0 < symNet m A g c t) := by sorry
