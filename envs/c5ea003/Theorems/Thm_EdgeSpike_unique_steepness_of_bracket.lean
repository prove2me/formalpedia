-- Prove2me | Theorems.Thm_EdgeSpike_unique_steepness_of_bracket
-- name    : EdgeSpike.unique_steepness_of_bracket
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:32:07.363874+00:00
-- url     : https://prove2.me/theorems/f669f7af-37b5-47ff-a219-899db0f553f4
-- title:
--   Population identification does hold.
-- statement:
--   **Population identification does hold.**  Whenever the observed edge mass is
--   bracketed by two model values, exactly one steepness reproduces it.  So the
--   non-identifiability audited here is a *tolerance* phenomenon (the ray of
--   `identified_ray`), not a failure of the population map: the model is injective
--   in `b`, but its image is exponentially compressed near the ceiling.
--
--   ```lean
--   theorem EdgeSpike.unique_steepness_of_bracket(hrho0 : 0 < rho) (ht0 : 0 < t) (ht1 : t < 1)
--       {v b₀ b₁ : ℝ} (hb0 : 0 < b₀) (hb01 : b₀ ≤ b₁)
--       (h1 : edgeProb rho t b₀ ≤ v) (h2 : v ≤ edgeProb rho t b₁) :
--       ∃! b : ℝ, b ∈ Set.Icc b₀ b₁ ∧ edgeProb rho t b = v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/EdgeSpikeCensoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/EdgeSpikeCensoring.lean#L434

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

theorem EdgeSpike.unique_steepness_of_bracket(hrho0 : 0 < rho) (ht0 : 0 < t) (ht1 : t < 1)
    {v b₀ b₁ : ℝ} (hb0 : 0 < b₀) (hb01 : b₀ ≤ b₁)
    (h1 : edgeProb rho t b₀ ≤ v) (h2 : v ≤ edgeProb rho t b₁) :
    ∃! b : ℝ, b ∈ Set.Icc b₀ b₁ ∧ edgeProb rho t b = v := by sorry
