-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_BivariateCyclePoisson
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_BivariateCyclePoisson
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T18:44:18.060812+00:00
-- url     : https://prove2.me/theorems/440a8d1c-5848-4928-95d2-fefc9956f433
-- title:
--   Joint two-cycle-count laws and product Poisson measures
-- statement:
--   One uniform permutation is pushed to the pair of cycle counts; the candidate limit is the product of two Poisson probability measures. Genuine joint PMFs divide simultaneous favorable counts by n!. Finite triangular support sets and products of one-dimensional inclusion-exclusion terms define their explicit formulas.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/BivariateCyclePoisson.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Bivariate Poisson limit for two cycle counts

This file proves the joint local limit and weak convergence of the pair of
cycle counts of two distinct positive lengths in a uniform random permutation.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace Bivariate

/-- Joint law of two fixed cycle counts under the uniform permutation measure. -/
def jointLaw (n r s : ℕ) : ProbabilityMeasure (ℕ × ℕ) :=
  ⟨Measure.map (fun σ : Equiv.Perm (Fin n) =>
      (rCycleCount n r σ, rCycleCount n s σ)) (uniformPermMeasure n),
    Measure.isProbabilityMeasure_map (by
      exact (measurable_of_finite _).aemeasurable)⟩

/-- Product of two Poisson probability measures. -/
def poissonProductMeasure (ρ τ : ℝ≥0) : ProbabilityMeasure (ℕ × ℕ) :=
  (poissonProbabilityMeasure ρ).prod (poissonProbabilityMeasure τ)

/-- The genuine joint pmf of two cycle counts. -/
def jointRCyclePMF (n r s i j : ℕ) : ℝ :=
  (Fintype.card {σ : Equiv.Perm (Fin n) //
    rCycleCount n r σ = i ∧ rCycleCount n s σ = j} : ℝ) / n.factorial

/-- One factor in the finite inclusion-exclusion series for `P(C_r=i)`. -/
def oneDimTerm (r i a : ℕ) : ℝ :=
  (((-1 : ℝ) ^ a) / (a.factorial * (i.factorial : ℝ))) *
    ((r : ℝ) ^ (-(i + a : ℤ)))

/-- The finite triangular index set where the exact mixed factorial moment is nonzero. -/
def jointIndexFinset (n r s i j : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n / r - i + 1)).product
      (Finset.range (n / s - j + 1))).filter
    (fun p : ℕ × ℕ => r * (i + p.1) + s * (j + p.2) ≤ n)

/-- The finite bivariate inclusion-exclusion expression. -/
def jointRCyclePMFFormula (n r s i j : ℕ) : ℝ :=
  ∑ p ∈ jointIndexFinset n r s i j,
    oneDimTerm r i p.1 * oneDimTerm s j p.2


end Bivariate
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics


