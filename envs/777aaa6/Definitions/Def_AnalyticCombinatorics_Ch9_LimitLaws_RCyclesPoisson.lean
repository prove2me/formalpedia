-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoisson
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:17:05.358158+00:00
-- url     : https://prove2.me/theorems/3cdb342b-50d2-4d21-b5b0-4ab1c12b785a
-- title:
--   Actual cycle-count laws and finite PMF formulas
-- statement:
--   poissonRate(r) is the nonnegative real inverse of r. uniformPermMeasure is the uniform measure on permutations of Fin n. rCycleCount counts fixed points when r=1 and otherwise the multiplicity of r in the nontrivial cycle type. Its pushforward, genuine favorable-count PMF divided by n!, finite exponential partial sums and inclusion-exclusion PMF formula are explicit mathematical objects.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/RCyclesPoisson.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_PMFToDistribution
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Cycles of a fixed length in a random permutation

This file sets up the genuine random variable counting cycles of length exactly
`r` in a uniform random permutation of `Fin n`.

For `r = 1` this is the fixed-point count.  For `r ≥ 2` it is the multiplicity
of `r` in Mathlib's `cycleType`, equivalently the number of nontrivial cycle
factors with support of cardinality `r`.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

/-- The Poisson rate `1 / r`, as a nonnegative real. -/
def poissonRate (r : ℕ) : ℝ≥0 :=
  (r : ℝ≥0)⁻¹

/-- Uniform probability measure on permutations of `Fin n`. -/
def uniformPermMeasure (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure

instance uniformPermMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (uniformPermMeasure n) := by
  unfold uniformPermMeasure
  infer_instance

/-- The Poisson law as a `ProbabilityMeasure`. -/
def poissonProbabilityMeasure (r : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨ProbabilityTheory.poissonMeasure r, ProbabilityTheory.isProbabilityMeasurePoisson r⟩

/-- The number of cycles of length exactly `r` in a permutation of `Fin n`.

Mathlib's `cycleType` records only nontrivial cycles, so `r = 1` is handled by
the fixed-point count. -/
def rCycleCount (n r : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  if r = 1 then FixedPointsPoissonNS.fixedPointCount n σ else σ.cycleType.count r

lemma rCycleCount_aemeasurable (n r : ℕ) :
    AEMeasurable (rCycleCount n r) (uniformPermMeasure n) :=
  (measurable_of_finite _).aemeasurable

/-- The law of the `r`-cycle count under the uniform permutation measure. -/
def rCycleLaw (n r : ℕ) : ProbabilityMeasure ℕ :=
  ⟨Measure.map (rCycleCount n r) (uniformPermMeasure n),
    Measure.isProbabilityMeasure_map (rCycleCount_aemeasurable n r)⟩

/-- Number of permutations of `Fin n` with exactly `j` cycles of length `r`. -/
def rCycleFavourableCount (n r j : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // rCycleCount n r σ = j}

/-- The genuine pmf of the `r`-cycle count under the uniform measure. -/
def rCyclePMF (n r j : ℕ) : ℝ :=
  (rCycleFavourableCount n r j : ℝ) / n.factorial

/-- Partial sums of the real exponential series, using `range m`. -/
def expPartial (x : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, x ^ i / i.factorial

/-- The standard inclusion-exclusion pmf expression for the number of `r`-cycles.

The theorem `rCyclePMFFormula_tendsto_poisson` proves the analytic limit of this
formula.  The remaining combinatorial step is to identify the genuine pmf
`rCyclePMF` with this expression. -/
def rCyclePMFFormula (n r j : ℕ) : ℝ :=
  if r = 0 then 0
  else if r * j ≤ n then
    (((r : ℝ) ^ j * j.factorial)⁻¹) *
      expPartial (-(r : ℝ)⁻¹) (n / r - j + 1)
  else 0

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics


