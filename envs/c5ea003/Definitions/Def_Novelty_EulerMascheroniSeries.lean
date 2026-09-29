-- Prove2me | Definitions.Def_Novelty_EulerMascheroniSeries
-- name    : Novelty_EulerMascheroniSeries
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:24:50.305327+00:00
-- url     : https://prove2.me/theorems/8f4dde46-099b-47d2-946d-56af9e5db796
-- title:
--   Aether Catalog definitions — Novelty_EulerMascheroniSeries
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EulerMascheroniSeries`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EulerMascheroniSeries.lean by skeleton subtraction
import Mathlib

/-!
# A convergent series representation of the Euler–Mascheroni constant

Mathlib defines `Real.eulerMascheroniConstant` as the limit of the sequence
`eulerMascheroniSeq n = H_n - log (n + 1)` and proves the basic monotone /
bracketing facts (`Real.tendsto_eulerMascheroniSeq`,
`Real.eulerMascheroniSeq_lt_eulerMascheroniConstant`, …).  It does **not**, however,
record `γ` as the *sum of an explicit convergent series*.

Here we prove the classical identity
$$ \gamma \;=\; \sum_{k=0}^{\infty}\Bigl(\tfrac{1}{k+1} - \log\tfrac{k+2}{k+1}\Bigr)
        \;=\; \sum_{m=1}^{\infty}\Bigl(\tfrac1m - \log(1+\tfrac1m)\Bigr). $$
Every term is nonnegative (because `log(1+x) ≤ x`), and the partial sums telescope
*exactly* onto Mathlib's `eulerMascheroniSeq`, so the series converges to `γ` as a
`HasSum`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the defining sequence `H_n - log(n+1)` is itself the
sequence of partial sums of the term-by-term series `1/m - log(1+1/m)`; if so, `γ`
is literally a sum of a nonnegative convergent series.
Experiment (Experimenter): formalize `partial_sum n = eulerMascheroniSeq n` by
splitting the finite sum and telescoping `∑ log((k+2)/(k+1)) = log(n+1)`; combine
with `hasSum_iff_tendsto_nat_of_nonneg` and `Real.tendsto_eulerMascheroniSeq`.
Analysis (Analyst): the telescoping is the crux — `∑_{k<n} log((k+2)/(k+1))`
collapses via `log_mul` to `log(n+1)`; the harmonic part is a routine cast.
The nonnegativity of every term is exactly the convexity bound `log x ≤ x - 1`.
Critique (Critic): `HasSum` is genuinely stronger than the bare `Filter.Tendsto` of
`range`-partial sums for a general series, but is *equivalent* here precisely
because the terms are nonnegative — `term_nonneg` is therefore load-bearing, not
decorative.  Removing it would make `hasSum_iff_tendsto_nat_of_nonneg`
inapplicable and the `HasSum` claim false in general.
Synthesis (PI): the series representation is the cleanest bridge from Mathlib's
limit definition to the "series acceleration / integral representation" theme, and
is reused downstream (`EulerMascheroniApprox`) to identify the tail with the
approximation error.
-- !-- end Lab Notes -- !--
-/

open Real Filter Finset Topology

namespace EulerMascheroniSeries

/-- The `k`-th series term `1/(k+1) - log((k+2)/(k+1)) = 1/(k+1) - log(1 + 1/(k+1))`. -/
noncomputable def term (k : ℕ) : ℝ := 1 / (k + 1 : ℝ) - Real.log ((k + 2) / (k + 1))








end EulerMascheroniSeries


