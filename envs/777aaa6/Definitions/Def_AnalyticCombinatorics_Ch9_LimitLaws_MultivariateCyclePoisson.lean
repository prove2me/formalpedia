-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_MultivariateCyclePoisson
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_MultivariateCyclePoisson
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T18:46:18.63543+00:00
-- url     : https://prove2.me/theorems/7eae923b-87b4-424d-bbf5-6d3b304ee691
-- title:
--   Finite cycle-count vectors and product laws
-- statement:
--   The actual law pushes one uniform permutation to all Fin m-indexed cycle counts simultaneously. The limiting ProbabilityMeasure.pi is a product of Poisson measures. Genuine simultaneous favorable-count PMFs, coordinatewise Poisson masses, finite triangular support sets and inclusion-exclusion sums are defined for the fixed finite vector space.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/MultivariateCyclePoisson.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_BivariateCyclePoisson
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Multivariate Poisson limits for finitely many cycle counts

This file contains the finite-product discrete bridge and the basic singleton
mass identities for vectors of cycle counts.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace Multivariate

/-- Joint law of finitely many fixed cycle counts under the uniform permutation measure. -/
def multivariateLaw {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ) :
    ProbabilityMeasure (Fin m → ℕ) :=
  ⟨Measure.map
      (fun σ : Equiv.Perm (Fin n) => fun i : Fin m => rCycleCount n (lengths i) σ)
      (uniformPermMeasure n),
    Measure.isProbabilityMeasure_map (by
      exact (measurable_of_finite _).aemeasurable)⟩

/-- Product of the marginal Poisson probability measures. -/
def poissonPiMeasure {m : ℕ} (lengths : Fin m → ℕ) :
    ProbabilityMeasure (Fin m → ℕ) :=
  ProbabilityMeasure.pi
    (fun i : Fin m => poissonProbabilityMeasure (poissonRate (lengths i)))

/-- The genuine joint pmf of finitely many cycle counts. -/
def multivariatePMF {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ) (v : Fin m → ℕ) : ℝ :=
  let p : Equiv.Perm (Fin n) → Prop := fun σ =>
    ∀ i : Fin m, rCycleCount n (lengths i) σ = v i
  let instDec : DecidablePred p := fun _ => Fintype.decidableForallFintype
  let instSub : Fintype {σ : Equiv.Perm (Fin n) // p σ} :=
    @Subtype.fintype (Equiv.Perm (Fin n)) p instDec _
  (@Fintype.card {σ : Equiv.Perm (Fin n) // p σ} instSub : ℝ) / n.factorial

/-- The limiting product Poisson pmf. -/
def poissonPiPMF {m : ℕ} (lengths : Fin m → ℕ) (v : Fin m → ℕ) : ℝ :=
  ∏ i : Fin m, ProbabilityTheory.poissonPMFReal (poissonRate (lengths i)) (v i)

/-- One factor in the finite inclusion-exclusion series for `P(C_r=i)`. -/
def oneDimTerm (r i a : ℕ) : ℝ := Bivariate.oneDimTerm r i a

/-- The finite triangular index set where the exact mixed factorial moment is nonzero. -/
def multivariateIndexFinset {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ)
    (v : Fin m → ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset
    (fun i : Fin m => Finset.range (n / lengths i - v i + 1))).filter
      (fun u : Fin m → ℕ => ∑ i : Fin m, lengths i * (v i + u i) ≤ n)

/-- The finite multivariate inclusion-exclusion expression. -/
def multivariatePMFFormula {m : ℕ} (n : ℕ) (lengths : Fin m → ℕ)
    (v : Fin m → ℕ) : ℝ :=
  ∑ u ∈ multivariateIndexFinset n lengths v,
    ∏ i : Fin m, oneDimTerm (lengths i) (v i) (u i)

-- The finite-product `HasSum` induction combines a dependent tail series with
-- `HasSum.mul`; the local heartbeat bump prevents a deterministic timeout in
-- the summability witness elaboration.

end Multivariate
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics


