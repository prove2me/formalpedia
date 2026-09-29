-- Prove2me | Theorems.Thm_EulerMascheroniSeries_partial_sum
-- name    : EulerMascheroniSeries.partial_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:47:43.849088+00:00
-- url     : https://prove2.me/theorems/0b2aa3e2-3865-42ae-b0d7-6a4e5ce3e97e
-- title:
--   The `n`-th partial sum of the series equals Mathlib's `eulerMascheroniSeq n`.
-- statement:
--   The `n`-th partial sum of the series equals Mathlib's `eulerMascheroniSeq n`.
--
--   ```lean
--   theorem EulerMascheroniSeries.partial_sum(n : ℕ) :
--       ∑ k ∈ range n, term k = Real.eulerMascheroniSeq n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EulerMascheroniSeries.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EulerMascheroniSeries.lean#L68

-- Thm stub generated from Novelty/EulerMascheroniSeries.lean
import Mathlib
import Definitions.Def_Novelty_EulerMascheroniSeries

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

open EulerMascheroniSeries

theorem EulerMascheroniSeries.partial_sum(n : ℕ) :
    ∑ k ∈ range n, term k = Real.eulerMascheroniSeq n := by sorry
