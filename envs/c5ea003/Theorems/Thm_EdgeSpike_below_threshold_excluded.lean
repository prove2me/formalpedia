-- Prove2me | Theorems.Thm_EdgeSpike_below_threshold_excluded
-- name    : EdgeSpike.below_threshold_excluded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:31:32.748537+00:00
-- url     : https://prove2.me/theorems/b01880c0-49f9-45e8-a3a9-a467e0e3bdb2
-- title:
--   Lower bounds do survive.
-- statement:
--   **Lower bounds do survive.**  Any steepness whose edge mass falls short of
--   the observed value by more than the tolerance is excluded, and by strict
--   monotonicity so is every smaller steepness.  Together with `identified_ray`
--   this is the amended verdict: the identified set for `b` is of the form
--   "`b ≳ b₁`", with no upper limit.
--
--   ```lean
--   theorem EdgeSpike.below_threshold_excluded(hrho0 : 0 < rho) (ht0 : 0 < t) (ht1 : t < 1)
--       {v eps b b₁ : ℝ} (heps : 0 ≤ eps) (hb : 0 < b) (hbb : b ≤ b₁)
--       (hexcl : edgeProb rho t b₁ + eps < v) :
--       eps < |edgeProb rho t b - v| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/EdgeSpikeCensoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/EdgeSpikeCensoring.lean#L413

-- Thm stub generated from MachineLearning/EdgeSpikeCensoring.lean
import Mathlib
import Definitions.Def_MachineLearning_EdgeSpikeCensoring

/-!
# Edge-spike censoring: why the steepness of a left-edge spike is a lower bound only

## Motivation (exp 594 / paper 245, round-88 identifiability audit)

A pooled positional histogram was fitted with a two-component profile,
*flat bulk + left-edge spike*, where the spike is an exponential law with rate
`b` truncated to the unit interval.  Empirically the fitted `b_edge` "rode the
cap": it landed at `40.000` when the optimiser was capped at `40` and at `40.46`
when capped at `80`, with a bootstrap CI `[15.25, 80.0]` whose upper end is the
cap itself.  The registered analysis therefore had to be amended to
*"left-edge spike with `b_edge ≳ 15`, **lower bound only**"*.

This file proves that this behaviour is **not** an artefact of the optimiser:
it is a theorem about the model class.  Once the observable is the *mass in the
edge bin* `[0, t]`, the map `b ↦` (edge mass) is strictly increasing but
bounded, and it approaches its ceiling at rate `exp (-b t)`.  Consequently:

* `EdgeSpike.binLogLik_cap_riding` — the binned log-likelihood is **strictly
  increasing in `b`** whenever the empirical edge fraction is at least the
  ceiling `edgeProbLimit`.  Hence for every cap `B` the constrained optimum sits
  exactly at `b = B`: cap-riding is forced.
* `EdgeSpike.no_finite_maximiser` — no finite maximiser exists, so no cap raise
  produces an interior optimum.
* `EdgeSpike.cap_gain_le` — the total remaining log-likelihood available above a
  cap `B` is at most `C · exp (-B t)`.  Raising the cap buys exponentially
  little: at the audited geometry this is why `dAICc` moved only from `-101.28`
  to `-101.33` between caps `40` and `80`.

The three statements together are the formal content of the verdict
`H0_SPIKE_STEEPNESS_UNIDENTIFIABLE`: the data censor the steepness parameter.
-/

open EdgeSpike

open Real Filter Topology






variable {b t : ℝ}










variable {t : ℝ}







variable {b t : ℝ}





variable {h p q rho t b : ℝ}










variable {rho t : ℝ}

theorem EdgeSpike.below_threshold_excluded(hrho0 : 0 < rho) (ht0 : 0 < t) (ht1 : t < 1)
    {v eps b b₁ : ℝ} (heps : 0 ≤ eps) (hb : 0 < b) (hbb : b ≤ b₁)
    (hexcl : edgeProb rho t b₁ + eps < v) :
    eps < |edgeProb rho t b - v| := by sorry
