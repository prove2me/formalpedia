-- Prove2me | Theorems.Thm_EdgeSpike_identified_ray
-- name    : EdgeSpike.identified_ray
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:31:54.964915+00:00
-- url     : https://prove2.me/theorems/73678e31-55fa-4926-9b63-518d2640bf7e
-- title:
--   The identified set contains a ray.
-- statement:
--   **The identified set contains a ray.**  If the observed edge mass `v` sits
--   within the tolerance `eps` of the ceiling, then *every* steepness above a
--   threshold `B₀` (any `B₀ ≥ 1` with `2 rho exp (-B₀ t) ≤ eps`) is compatible with
--   the data: there is no finite upper confidence limit for `b`.
--
--   ```lean
--   theorem EdgeSpike.identified_ray(hrho0 : 0 < rho) (hrho1 : rho < 1) (ht0 : 0 < t) (ht1 : t < 1)
--       {v eps B₀ b : ℝ} (hv1 : edgeProbLimit rho t - eps ≤ v)
--       (hv2 : v ≤ edgeProbLimit rho t) (hB0 : 1 ≤ B₀)
--       (hB0' : 2 * rho * exp (-(B₀ * t)) ≤ eps) (hb : B₀ ≤ b) :
--       |edgeProb rho t b - v| ≤ eps := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/EdgeSpikeCensoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/EdgeSpikeCensoring.lean#L374

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

theorem EdgeSpike.identified_ray(hrho0 : 0 < rho) (hrho1 : rho < 1) (ht0 : 0 < t) (ht1 : t < 1)
    {v eps B₀ b : ℝ} (hv1 : edgeProbLimit rho t - eps ≤ v)
    (hv2 : v ≤ edgeProbLimit rho t) (hB0 : 1 ≤ B₀)
    (hB0' : 2 * rho * exp (-(B₀ * t)) ≤ eps) (hb : B₀ ≤ b) :
    |edgeProb rho t b - v| ≤ eps := by sorry
