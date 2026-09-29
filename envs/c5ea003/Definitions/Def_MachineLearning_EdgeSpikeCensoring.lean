-- Prove2me | Definitions.Def_MachineLearning_EdgeSpikeCensoring
-- name    : MachineLearning_EdgeSpikeCensoring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:47.854986+00:00
-- url     : https://prove2.me/theorems/db882168-fc4d-4fc8-bb18-48a02b70697b
-- title:
--   Aether Catalog definitions — MachineLearning_EdgeSpikeCensoring
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.EdgeSpikeCensoring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/EdgeSpikeCensoring.lean by skeleton subtraction
import Mathlib

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

namespace EdgeSpike

open Real Filter Topology

/-- CDF at `t` of the exponential law with rate `b` truncated to `[0,1]`;
this is the mass that a left-edge spike of steepness `b` puts in the edge bin
`[0, t]`. -/
noncomputable def truncExpCDF (b t : ℝ) : ℝ := (1 - exp (-(b * t))) / (1 - exp (-b))

/-- Edge-bin probability of the *flat bulk + left-edge spike* profile:
a fraction `1 - rho` of the mass is uniform on `[0,1]` and a fraction `rho`
follows the truncated exponential of steepness `b`. -/
noncomputable def edgeProb (rho t b : ℝ) : ℝ := (1 - rho) * t + rho * truncExpCDF b t

/-- The `b → ∞` ceiling of `edgeProb`: the spike degenerates to a point mass at
the left edge, i.e. the whole spike component lands in the edge bin. -/
noncomputable def edgeProbLimit (rho t : ℝ) : ℝ := (1 - rho) * t + rho

/-- Per-observation binned log-likelihood of the two-cell (edge vs. bulk) table
with empirical edge fraction `h` and model edge probability `p`. -/
noncomputable def binLogLik (h p : ℝ) : ℝ := h * log p + (1 - h) * log (1 - p)

section Basic

variable {b t : ℝ}





end Basic

section Convexity


end Convexity

section Monotone

variable {t : ℝ}





end Monotone

section Censoring

variable {b t : ℝ}



end Censoring

section Likelihood

variable {h p q rho t b : ℝ}








end Likelihood

section IdentifiedSet

variable {rho t : ℝ}





end IdentifiedSet

end EdgeSpike


