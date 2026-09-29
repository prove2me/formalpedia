-- Prove2me | Definitions.Def_NumberTheory_ProfileFormExponentThreshold
-- name    : NumberTheory_ProfileFormExponentThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:49.714303+00:00
-- url     : https://prove2.me/theorems/44415e9d-db7a-4385-874b-7be48c29573a
-- title:
--   Aether Catalog definitions — NumberTheory_ProfileFormExponentThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ProfileFormExponentThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ProfileFormExponentThreshold.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPowerLaw

/-!
# Profile form IV: the exponent-one threshold that the bootstrap straddles

Context (experiment 579, paper 229).  The fitted exponent of the positional
profile is `b ≈ 1.104` with cluster-bootstrap interval `b ∈ [0.991, 1.218]`.
That interval contains `1`, and `b = 1` is not an arbitrary number: it is the
exact threshold at which the total window mass of the profile changes from
divergent to finite.  Here we prove the threshold and then prove that the
measured interval genuinely straddles it, i.e. the experiment as it stands
cannot decide the qualitative question.

* `windowMass_eq` — closed form `∫₀^X (1+x)^(-b) dx = ((1+X)^(1-b) - 1)/(1-b)`
  for `b ≠ 1`;
* `windowMass_eq_log` — the harmonic case `b = 1` gives exactly `log (1+X)`;
* `windowMass_tendsto_finite` — for `b > 1` the total mass converges to
  `1/(b-1)`;
* `windowMass_tendsto_atTop` — for `b ≤ 1` it diverges;
* `exponent_bootstrap_straddles_threshold` — inside the bootstrap interval
  `[0.991, 1.218]` both behaviours occur;
* `harmonic_sum_ge_log` — the discrete counterpart: the harmonic hit counts of
  the critical profile `b = 1` dominate `log (n+1)`, so the divergence is
  visible already at the level of counted hits.
-/

namespace ProfileForm

open Real Filter Topology intervalIntegral

/-- Total profile mass accumulated across the window `[0, X]`, at unit
amplitude. -/
noncomputable def windowMass (b X : ℝ) : ℝ := ∫ x in (0:ℝ)..X, (1 + x) ^ (-b)






/-! ## The discrete counterpart -/


end ProfileForm


