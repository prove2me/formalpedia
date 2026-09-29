-- Prove2me | Theorems.Thm_EdgeSpike_truncExpCDF_tendsto
-- name    : EdgeSpike.truncExpCDF_tendsto
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:31:49.754989+00:00
-- url     : https://prove2.me/theorems/386c7fc6-1857-45f0-8c3b-98e140b142fd
-- title:
--   The edge mass tends to its ceiling as the steepness grows.
-- statement:
--   The edge mass tends to its ceiling as the steepness grows.
--
--   ```lean
--   theorem EdgeSpike.truncExpCDF_tendsto(ht0 : 0 < t) (ht1 : t ≤ 1) :
--       Tendsto (fun b => truncExpCDF b t) atTop (𝓝 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/EdgeSpikeCensoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/EdgeSpikeCensoring.lean#L194

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

theorem EdgeSpike.truncExpCDF_tendsto(ht0 : 0 < t) (ht1 : t ≤ 1) :
    Tendsto (fun b => truncExpCDF b t) atTop (𝓝 1) := by sorry
