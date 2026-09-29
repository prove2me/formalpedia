-- Prove2me | Theorems.Thm_ProfileForm_harmonic_sum_ge_log
-- name    : ProfileForm.harmonic_sum_ge_log
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:36:52.861163+00:00
-- url     : https://prove2.me/theorems/3584af48-973d-4692-b73a-c7acc7a31e2f
-- title:
--   The counted-hit version of the critical profile: the harmonic sum dominates
-- statement:
--   The counted-hit version of the critical profile: the harmonic sum dominates
--   `log (n+1)`, so the divergence at `b = 1` is already visible in the counts.
--
--   ```lean
--   theorem ProfileForm.harmonic_sum_ge_log(n : ℕ) :
--       Real.log (n + 1) ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / (j + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormExponentThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormExponentThreshold.lean#L157

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







/-! ## The discrete counterpart -/

theorem ProfileForm.harmonic_sum_ge_log(n : ℕ) :
    Real.log (n + 1) ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / (j + 1) := by sorry
