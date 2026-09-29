-- Prove2me | Theorems.Thm_WhichFactorWall_binEntropy_conjectured_lower_bound_false
-- name    : WhichFactorWall.binEntropy_conjectured_lower_bound_false
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:01:33.823493+00:00
-- url     : https://prove2.me/theorems/343acfc5-8fb9-4659-980c-6b631e9afb4f
-- title:
--   The mission conjecture is false.
-- statement:
--   **The mission conjecture is false.**  There is no inverse-Lipschitz bound with the
--   supremum constant `c(δ) = log ((1-δ)/δ)` on `[δ, 1/2]`.  Witness: `δ = q = 1/4`,
--   `p = 1/2`, where the claim collapses to `log 27 ≤ log 16`.
--
--   ```lean
--   theorem WhichFactorWall.binEntropy_conjectured_lower_bound_false:
--       ¬ ∀ δ p q : ℝ, 0 < δ → δ ≤ 2⁻¹ → p ∈ Icc δ 2⁻¹ → q ∈ Icc δ 2⁻¹ →
--         log ((1 - δ) / δ) * |p - q| ≤ |binEntropy p - binEntropy q| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/WhichFactorWallInvariant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/WhichFactorWallInvariant.lean#L169

-- Thm stub generated from Algebra/WhichFactorWallInvariant.lean
import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
/-
# The which-factor wall as a cross-population invariant: how much does it really pin down?

This file continues `Speculative.AutoResearch.TraceBatteryWall`
(`TraceBattery.binary_wall_inversion`), which shows that a *binary* capacity
("wall") value determines the class imbalance of a two-valued statistic
**uniquely** on the balanced side `[0, 1/2]`.  Uniqueness, however, is a
qualitative statement.  The research question of this cycle is quantitative:

> if two independent populations report walls that agree to within `ε`,
> how close are their class imbalances?

The mission proposal was:

  `|binEntropy p - binEntropy q| ≥ c(δ) |p - q|` on `[δ, 1/2]`,
  with `c(δ) = log ((1-δ)/δ)`.

**This is false**, and `binEntropy_conjectured_lower_bound_false` refutes it with
an exact counterexample (`δ = q = 1/4`, `p = 1/2`), where the failure reduces to
`log 16 ≤ log 27`.  The reason is structural: `c(δ)` is the *supremum* of
`|binEntropy'|` on `[δ, 1/2]`, not its infimum, so it controls the Lipschitz
(upper) bound, while the true inverse bound must be governed by the derivative
at the endpoint *closest to* `1/2`.

What survives, and is proved here with zero sorries:

* `binEntropy_sub_ge` — the sharp mean-value lower bound
  `(q - p) * (log (1-q) - log q) ≤ binEntropy q - binEntropy p` for
  `0 ≤ p ≤ q ≤ 1/2` (including the boundary case `p = 0`).
* `binEntropy_lipschitz` — the true version of the proposed inequality, with the
  inequality reversed: `|binEntropy p - binEntropy q| ≤ c(δ) |p - q|` on
  `[δ, 1-δ]`.
* `imbalance_dist_le` / `imbalance_dist_le_div` — the corrected **cross-population
  stability theorem**: imbalances in `[0, 1/2 - η]` whose walls agree within `ε`
  agree within `ε / log ((1/2+η)/(1/2-η))`.
* `binary_wall_stability` — the same statement at the level of two binary
  statistics on two different finite populations, via the empirical entropy `H`.
* `log_two_sub_binEntropy_le_sq` — `log 2 - binEntropy (1/2 - t) ≤ 4 t²`, and
  `no_uniform_inversion_constant`: **no** constant inverts the wall near `1/2`.
  So the guard `η > 0` is not an artefact: the wall genuinely loses all
  resolution at balance, at a quadratic rate.
* `wall_imbalance_bracket` — the reported wall `0.4677` bits is a falsifiable
  claim about the split: the unique minority fraction in `[0, 1/2]` realising it
  lies strictly between `1/12` and `1/9` (i.e. between 8.34% and 11.11%),
  consistent with the reported 9.96% and inconsistent with, say, a 5% or a 15%
  split.

Because the catalog module `Combinatorics.TraceBatteryEntropy` carrying the
empirical-entropy definitions is not present in this snapshot, the small
population layer (`img`, `cnt`, `H`, `H_two_values`) is restated here in the
open `WhichFactorWall`,
self-contained and compiles on its own.
-/

open WhichFactorWall

open Real Set

/-! ## 1.  Mean-value machinery for `Real.binEntropy`

`binEntropy` is differentiable away from `{0,1}` with derivative
`log (1-x) - log x` (Mathlib's `Real.deriv_binEntropy`).  We turn one-sided
bounds on that derivative into slope bounds by monotonicity of an auxiliary
function; this is the mean value theorem in the form we need. -/







/-! ## 2.  Refutation of the proposed inverse bound -/

theorem WhichFactorWall.binEntropy_conjectured_lower_bound_false:
    ¬ ∀ δ p q : ℝ, 0 < δ → δ ≤ 2⁻¹ → p ∈ Icc δ 2⁻¹ → q ∈ Icc δ 2⁻¹ →
      log ((1 - δ) / δ) * |p - q| ≤ |binEntropy p - binEntropy q| := by sorry
