-- Prove2me | Definitions.Def_Applications_EulerMascheroni_SeriesRepresentation
-- name    : Applications_EulerMascheroni_SeriesRepresentation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:56.116957+00:00
-- url     : https://prove2.me/theorems/1e2f3758-33ab-4354-9f31-c22e5a6807cb
-- title:
--   Aether Catalog definitions — Applications_EulerMascheroni_SeriesRepresentation
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.EulerMascheroni.SeriesRepresentation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/EulerMascheroni/SeriesRepresentation.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Euler–Mascheroni Constant: An Accelerated, Manifestly Convergent Series

This file develops a *manifestly convergent* series representation of the
Euler–Mascheroni constant `γ = lim (H_n - log n)` built on Mathlib's
`eulerMascheroniConstant`, together with a sharp two-sided rational
approximation error bound.

The classical definition of `γ` as `lim (H_n - log(n+1))` is a difference of two
quantities that each diverge.  We package the *increments* of the defining
sequence into a single series whose `k`-th term

  `gammaTerm k = 1/(k+1) - (log(k+2) - log(k+1)) = 1/(k+1) - log(1 + 1/(k+1))`

is *nonnegative* (because `log(1+x) ≤ x`), so the resulting series converges
unconditionally and its partial sums equal the defining sequence exactly.

## Main results

- `EMR.sum_gammaTerm` : the `n`-th partial sum of `gammaTerm` telescopes
  exactly to `eulerMascheroniSeq n = H_n - log(n+1)`.
- `EMR.gammaTerm_nonneg` : every term is nonnegative.
- `EMR.hasSum_gammaTerm` : `HasSum gammaTerm eulerMascheroniConstant`, i.e.
  `γ = ∑_{k} (1/(k+1) - log(1 + 1/(k+1)))` as an unconditionally convergent sum.
- `EMR.tsum_gammaTerm` : `∑' k, gammaTerm k = γ`.
- `EMR.approx_error_bound` : for `n ≥ 1` the lower-sequence approximation is
  good to within `log(n+1) - log n = log(1 + 1/n)`:
    `0 < γ - (H_n - log(n+1)) < log(n+1) - log n`.

These give explicit, computable, *rational-plus-logarithm* approximations to `γ`
with a controlled (`O(1/n)`) error — the natural starting point for
irrationality investigations (see `IrrationalityCriterion.lean`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The defining sequence `H_n - log(n+1)` for `γ`, being
monotone increasing and bounded, must arise as the partial sums of a nonnegative
series; identifying that series gives an "accelerated" (manifestly convergent)
representation and a clean error bound.

Experiment (Experimenter): Defined `gammaTerm k = 1/(k+1) - (log(k+2)-log(k+1))`.
Proved the partial sums telescope to `eulerMascheroniSeq n` (`sum_gammaTerm`,
via induction for the log part and a cast identity for the harmonic part).
Nonnegativity follows from `Real.log_le_sub_one_of_pos` applied to `(k+2)/(k+1)`.
Summability from `summable_of_sum_range_le` with the ceiling `γ` provided by
Mathlib's `eulerMascheroniSeq_lt_eulerMascheroniConstant`.

Analysis (Analyst): The key structural insight is that `1/(k+1) - log(1+1/(k+1))`
is exactly the "overshoot" of the harmonic increment over the logarithmic
increment, and that this overshoot is provably nonnegative — turning a
difference of divergent series into a convergent series of positive terms.
The error bound is exactly the gap between Mathlib's lower sequence
`H_n - log(n+1)` and upper sequence `H_n - log n`.

Critique (Critic): The HasSum statement is NOT a definitional rewrite: it
upgrades the `Tendsto` of `range`-partial-sums to an unconditional `HasSum`,
which requires genuine summability.  The error bound is strict on both sides and
uses the strict monotonicity/antitonicity of the two Mathlib sequences.  No
`native_decide`, no vacuity.

Synthesis (PI): `γ` now has a manifestly convergent series and a sharp
`O(1/n)` rational-plus-log approximation, feeding the irrationality work.
-- !-- Lab Notes -- !--
-/

open Real Filter Topology
open scoped BigOperators

namespace EMR

/-- The `k`-th term of the accelerated series for the Euler–Mascheroni constant:
`1/(k+1) - (log(k+2) - log(k+1)) = 1/(k+1) - log(1 + 1/(k+1))`. -/
noncomputable def gammaTerm (k : ℕ) : ℝ :=
  1 / (k + 1) - (Real.log (k + 2) - Real.log (k + 1))









end EMR


