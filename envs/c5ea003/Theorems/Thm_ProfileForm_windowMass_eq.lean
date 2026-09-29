-- Prove2me | Theorems.Thm_ProfileForm_windowMass_eq
-- name    : ProfileForm.windowMass_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:39:01.20378+00:00
-- url     : https://prove2.me/theorems/b84fe2a2-86b5-4ec3-ac41-63513f41bf7b
-- title:
--   Closed form of the window mass away from the critical exponent.
-- statement:
--   Closed form of the window mass away from the critical exponent.
--
--   ```lean
--   theorem ProfileForm.windowMass_eq{b X : ℝ} (hb : b ≠ 1) (hX : 0 ≤ X) :
--       windowMass b X = ((1 + X) ^ (1 - b) - 1) / (1 - b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormExponentThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormExponentThreshold.lean#L35

-- Thm stub generated from NumberTheory/ProfileFormExponentThreshold.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormExponentThreshold
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

open ProfileForm

open Real Filter Topology intervalIntegral

theorem ProfileForm.windowMass_eq{b X : ℝ} (hb : b ≠ 1) (hX : 0 ≤ X) :
    windowMass b X = ((1 + X) ^ (1 - b) - 1) / (1 - b) := by sorry
