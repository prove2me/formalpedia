-- Prove2me | Definitions.Def_Algebra_WhichFactorWallInvariant
-- name    : Algebra_WhichFactorWallInvariant
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:21:49.727645+00:00
-- url     : https://prove2.me/theorems/f258aed5-d05f-4f9b-88cb-887fa34cf8cc
-- title:
--   Aether Catalog definitions — Algebra_WhichFactorWallInvariant
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.WhichFactorWallInvariant`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/WhichFactorWallInvariant.lean by skeleton subtraction
import Mathlib
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
namespace `WhichFactorWall`, with the same definitions, so that the file is
self-contained and compiles on its own.
-/

namespace WhichFactorWall

open Real Set

/-! ## 1.  Mean-value machinery for `Real.binEntropy`

`binEntropy` is differentiable away from `{0,1}` with derivative
`log (1-x) - log x` (Mathlib's `Real.deriv_binEntropy`).  We turn one-sided
bounds on that derivative into slope bounds by monotonicity of an auxiliary
function; this is the mean value theorem in the form we need. -/







/-! ## 2.  Refutation of the proposed inverse bound -/


/-! ## 3.  Corrected cross-population stability -/



/-! ## 4.  Why the guard `η > 0` cannot be dropped: quadratic degeneracy at balance -/



/-! ## 5.  Population layer: empirical entropy of a two-valued statistic

These are the definitions of the catalog's trace-battery entropy module,
restated so that this file is self-contained. -/

section Population

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α : Type*}

/-- The set of readings actually attained by a statistic. -/
noncomputable def img [DecidableEq α] (f : Ω → α) : Finset α := Finset.image f Finset.univ

/-- The number of population members with a given reading. -/
noncomputable def cnt [DecidableEq α] (f : Ω → α) (a : α) : ℕ :=
  (Finset.univ.filter fun w => f w = a).card

/-- Empirical (Shannon) entropy of a statistic, in nats. -/
noncomputable def H [DecidableEq α] (f : Ω → α) : ℝ :=
  ∑ a ∈ img f, ((cnt f a : ℝ) / (Fintype.card Ω : ℝ)) *
    Real.log ((Fintype.card Ω : ℝ) / (cnt f a : ℝ))

variable [DecidableEq α]




end Population


/-! ## 6.  The reported wall `0.4677` bits as a falsifiable claim about the split -/












end WhichFactorWall


