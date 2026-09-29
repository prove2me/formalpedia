-- Prove2me | Definitions.Def_Novelty_FyodorovHiaryKeating
-- name    : Novelty_FyodorovHiaryKeating
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:26:32.44897+00:00
-- url     : https://prove2.me/theorems/7fa6f39f-217d-4f05-8f21-04fa0cc7a7ed
-- title:
--   Aether Catalog definitions — Novelty_FyodorovHiaryKeating
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FyodorovHiaryKeating`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FyodorovHiaryKeating.lean by skeleton subtraction
import Mathlib

/-!
# The Gumbel law and extreme-value convergence: the analytic backbone of the
  Fyodorov–Hiary–Keating conjecture

The Fyodorov–Hiary–Keating (FHK) conjecture predicts that the maximum of
`log |ζ(1/2 + it)|` over a unit-scale window `[T, 2T]`, after the centering
`M_T - log log T + (3/2) log log log T`, converges in distribution to the sum of
two independent **Gumbel** random variables (Fyodorov–Hiary–Keating, 2012;
leading-order results by Arguin–Belius–Harper, 2017).

The full conjecture for `ζ` is open and far outside the reach of current
formalization.  This file instead formalizes the *rigorous analytic backbone* of
the statement: the Gumbel distribution itself and the extreme-value limit theorem
that produces it.  Concretely we prove:

* `gumbelCDF` is a genuine cumulative distribution function: strictly positive,
  bounded by `1`, strictly increasing, continuous, with the correct limits `0`
  and `1` at `±∞` (`gumbelCDF_pos`, `gumbelCDF_lt_one`, `gumbelCDF_strictMono`,
  `gumbelCDF_continuous`, `gumbelCDF_tendsto_atBot`, `gumbelCDF_tendsto_atTop`).

* **Max-stability of the Gumbel law** (`gumbel_max_stable`): raising the Gumbel
  CDF at the shifted point `x + log n` to the power `n` recovers `gumbelCDF x`.
  This exact algebraic self-similarity is *the* reason the Gumbel law is the
  universal attractor of maxima.

* **Extreme-value convergence** (`tendsto_expMax_gumbel`): the CDF of the
  recentered maximum of `n` i.i.d. `Exp(1)` variables, `(1 - e^{-x}/n)^n`,
  converges pointwise to `gumbelCDF x`.  This is the Fisher–Tippett–Gnedenko
  limit in the domain of attraction of the Gumbel law — the simplest exact
  instance of the phenomenon underlying FHK.

* The Gumbel probability density `gumbelPDF` is the derivative of `gumbelCDF`
  (`hasDerivAt_gumbelCDF`), is strictly positive (`gumbelPDF_pos`), and
  integrates to `1` over the whole line (`gumbelPDF_integral_eq_one`), so it is a
  genuine probability density.

* The Gumbel median is `-log(log 2)` (`gumbelCDF_median`).

All statements are elementary real analysis, but together they establish that the
object appearing in the FHK conjecture is a bona fide probability law arising as
an extreme-value limit.
-/

open Filter Topology MeasureTheory
open scoped Topology

namespace FHK

/-- The standard **Gumbel** cumulative distribution function
`G(x) = exp(-exp(-x))`. -/
noncomputable def gumbelCDF (x : ℝ) : ℝ := Real.exp (-Real.exp (-x))

/-- The standard **Gumbel** probability density
`g(x) = exp(-x - exp(-x))`, the derivative of `gumbelCDF`. -/
noncomputable def gumbelPDF (x : ℝ) : ℝ := Real.exp (-x - Real.exp (-x))













/-!
### The location–scale Gumbel family

We lift the standard Gumbel law to the two-parameter location–scale family
`G_{μ,β}(x) = exp(-exp(-(x-μ)/β))` with location `μ` and scale `β > 0`, and
recover positivity, boundedness, strict monotonicity, continuity, and the exact
max-stability `G_{μ,β}(x + β log n)^n = G_{μ,β}(x)` (the form directly relevant to
recentered maxima with a nontrivial scale).
-/

/-- The **location–scale Gumbel** CDF `G_{μ,β}(x) = exp(-exp(-(x-μ)/β))`. -/
noncomputable def gumbelCDFLS (μ β x : ℝ) : ℝ := Real.exp (-Real.exp (-((x - μ) / β)))








end FHK


