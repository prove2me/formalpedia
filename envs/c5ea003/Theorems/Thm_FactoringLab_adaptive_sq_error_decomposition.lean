-- Prove2me | Theorems.Thm_FactoringLab_adaptive_sq_error_decomposition
-- name    : FactoringLab.adaptive_sq_error_decomposition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:29:28.941979+00:00
-- url     : https://prove2.me/theorems/cae295f6-f05c-4f62-8143-1417ea043366
-- title:
--   Exact error decomposition for adaptive strategies.
-- statement:
--   **Exact error decomposition for adaptive strategies.**  The squared error of
--   an `N`-only adaptive strategy splits into the irreducible band-conditional
--   error plus the strategy's squared deviation from the band mean.
--
--   ```lean
--   theorem FactoringLab.adaptive_sq_error_decomposition[DecidableEq κ]
--       (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
--       (t : DTree ι) (ht : t.BandOnly Ω n) :
--       ∑ i ∈ Ω, (t.eval i - Y i) ^ 2
--         = ∑ i ∈ Ω, (t.eval i - bandMean Ω n Y i) ^ 2
--           + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AdaptiveBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AdaptiveBarrier.lean#L157

-- Thm stub generated from Probability/AdaptiveBarrier.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_StructuralOrthogonality
/-
# The Adaptive Barrier (Factoring Lab, Phase A v19c — cycle 2)

Closing **Conjecture 5** of `FUTURE_DIRECTIONS.md`: *the structural-orthogonality
barrier is closed under adaptivity.*

The previous cycle proved that no invariant `g ∘ n` computable from the band
label alone predicts the target better than the band mean
(`FactoringLab.bandMean_is_best_predictor`), and that arbitrary *fixed*
nonlinear aggregation `Φ(w₁, …, w_m)` of finitely many free witnesses stays
`N`-only (`FactoringLab.aggregation_no_better_than_bandMean`).

An obvious escape route is *adaptivity*: run an `N`-only test, and depending on
its outcome run a different test, and so on, finally emitting a candidate
factor.  This file formalizes such a strategy as a finite **decision tree**
whose internal tests and whose leaf outputs are band-measurable, and proves:

* `FactoringLab.DTree.bandMeasurable_eval` — the value computed by such a tree
  is itself band-measurable (structural induction on the tree);
* `FactoringLab.factors_through_band` — every band-measurable function factors
  as `g ∘ n` for some `g : κ → ℝ`;
* `FactoringLab.adaptive_structural_orthogonality` — the output of any such
  tree is orthogonal to the residual `Y − E[Y | n]`;
* `FactoringLab.adaptive_barrier` — no such tree beats the band mean, *for any
  depth and any branching*; the excess error is again exactly the squared
  deviation from the band mean (`adaptive_sq_error_decomposition`);
* `FactoringLab.adaptive_cov_eq_cov_bandMean` and
  `FactoringLab.adaptive_nearEqualN_test` — the near-equal-`N` test applies
  verbatim to adaptive strategies: constant band means force covariance `0`.

Boundary (Stage 4, adversarial review).  The band-measurability hypothesis is
not decorative: `FactoringLab.adaptive_barrier_fails_without_bandMeasurable`
exhibits a two-point population and a depth-`0` tree which attains error `0`
while the band mean has error `1/2`.

Finally `FactoringLab.witnessTree_bandMeasurable` shows the hypothesis is met
by the strategies the framework is about: any tree whose tests are threshold
comparisons of free witnesses `w : κ → ℝ` and whose leaves are `N`-only
invariants is band-measurable, so the barrier covers the whole adaptive
free-witness family.
-/

open Finset

open FactoringLab

variable {ι κ : Type*}

/-! ## 1.  Band-measurable functions -/






/-! ## 2.  Adaptive strategies as decision trees -/


open DTree







/-! ## 3.  The adaptive barrier -/

theorem FactoringLab.adaptive_sq_error_decomposition[DecidableEq κ]
    (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
    (t : DTree ι) (ht : t.BandOnly Ω n) :
    ∑ i ∈ Ω, (t.eval i - Y i) ^ 2
      = ∑ i ∈ Ω, (t.eval i - bandMean Ω n Y i) ^ 2
        + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2 := by sorry
