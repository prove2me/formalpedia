-- Prove2me | Theorems.Thm_EdgeSpike_cap_gain_le
-- name    : EdgeSpike.cap_gain_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:31:40.525765+00:00
-- url     : https://prove2.me/theorems/cb111c97-e910-41a4-a36f-cc5947655931
-- title:
--   Exponentially small cap gains.
-- statement:
--   **Exponentially small cap gains.**  All the log-likelihood that remains
--   above a cap `b` is bounded by `C · exp (-b t)` with
--   `C = 2 rho / min ((1-rho) t) (1 - edgeProbLimit rho t)`.  Raising the cap
--   therefore buys exponentially little, whatever the data.
--
--   ```lean
--   theorem EdgeSpike.cap_gain_le(hrho0 : 0 < rho) (hrho1 : rho < 1) (ht0 : 0 < t) (ht1 : t < 1)
--       (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hb : 1 ≤ b) :
--       binLogLik h (edgeProbLimit rho t) - binLogLik h (edgeProb rho t b) ≤
--         (2 * rho / min ((1 - rho) * t) (1 - edgeProbLimit rho t)) * exp (-(b * t)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/EdgeSpikeCensoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/EdgeSpikeCensoring.lean#L315

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

theorem EdgeSpike.cap_gain_le(hrho0 : 0 < rho) (hrho1 : rho < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hb : 1 ≤ b) :
    binLogLik h (edgeProbLimit rho t) - binLogLik h (edgeProb rho t b) ≤
      (2 * rho / min ((1 - rho) * t) (1 - edgeProbLimit rho t)) * exp (-(b * t)) := by sorry
