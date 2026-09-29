-- Prove2me | Definitions.Def_MachineLearning_EulerMascheroni_SeriesRepresentation
-- name    : MachineLearning_EulerMascheroni_SeriesRepresentation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:52.456292+00:00
-- url     : https://prove2.me/theorems/ce07566d-9e72-4876-91e1-f2a912b5a2a8
-- title:
--   Aether Catalog definitions — MachineLearning_EulerMascheroni_SeriesRepresentation
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.EulerMascheroni.SeriesRepresentation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/EulerMascheroni/SeriesRepresentation.lean by skeleton subtraction
import Mathlib

/-!
# A positive-term series representation of the Euler–Mascheroni constant

This file establishes the classical *series acceleration* of the
Euler–Mascheroni constant `γ = eulerMascheroniConstant`:
```
γ = ∑_{k=0}^∞ ( 1/(k+1) − [log(k+2) − log(k+1)] ).
```
Every term `gterm k = 1/(k+1) − log((k+2)/(k+1))` is **strictly positive**
(because `log(1+x) < x`), so the partial sums increase monotonically to `γ`.
The `n`-th partial sum is *exactly* `eulerMascheroniSeq n = H_n − log(n+1)`, the
lower approximant from Mathlib, which makes this the "Apéry-like" monotone
rational-driven approximation to `γ`: the rational engine is the harmonic
number `H_n`, corrected by `log(n+1)`.

-- !-- Lab Notes -- !--
HYPOTHESIS.  `γ`, defined as `lim (H_n − log n)`, should equal a convergent
series of *positive* terms.  Telescoping `log(n+1) = ∑_{k<n}(log(k+2)−log(k+1))`
turns `H_n − log(n+1)` into a partial sum of `gterm`.

EXPERIMENT.  `gterm_partial` (induction + `harmonic_succ`) proves the partial-sum
identity.  `gterm_pos` derives positivity from `Real.log_lt_sub_one_of_pos`.
`hasSum_gterm` upgrades the convergence `eulerMascheroniSeq → γ` to a `HasSum`
statement using `summable_of_sum_range_le` (terms are nonnegative and partial
sums are bounded by `γ`) and uniqueness of limits.

ANALYSIS.  The representation is genuine but converges only like `1/k` (the term
`gterm k ~ 1/(2(k+1)^2)`, summable but slow).  The monotone lower approximants
`eulerMascheroniSeq n` are `H_n − log(n+1)`; their *rational* part `H_n` is the
Apéry-like data, but the additive logarithm prevents a purely rational sandwich
— this is the structural obstruction to an elementary irrationality proof.

CRITIQUE.  `hasSum_gterm` is not vacuous: it pins the sum to the specific value
`γ`, not merely "some real".  Positivity (`gterm_pos`) and strict monotonicity
(`strictMono_eulerMascheroniSeq`) are quantitative and use real inequalities.

SYNTHESIS.  We obtain a clean positive-term series for `γ`, the exact
identification of its partial sums with Mathlib's lower approximant, and strict
monotonicity of that approximant.
-/

open Filter Topology Real

namespace EulerMascheroni

/-- The `k`-th term of the positive series for `γ`:
`gterm k = 1/(k+1) − (log(k+2) − log(k+1))`. -/
noncomputable def gterm (k : ℕ) : ℝ :=
  (1 : ℝ) / (k + 1) - (Real.log (k + 2) - Real.log (k + 1))








end EulerMascheroni


