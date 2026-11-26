-- Prove2me | solution 1 for ReweightedNPMLE.probability_optimizer_iff_mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:14:41.248797+00:00
-- url     : https://prove2.me/submissions/cfc8b679-1e53-411f-b2cd-f43dd1bd0afd

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_fittedValue_maximizer_unique
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_nonempty_of_mem_convexHull

-- Inline helpers preserved from ReweightedNPMLE.ProbabilityOptimizerFiber.
section
/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





















theorem probabilityMixtureValue_eq_integral {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue A μ = ∫ θ, A θ ∂μ := by
  have hi := hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A)
    (μ := (μ : Measure Θ))
  funext i
  exact (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi

theorem probabilityMixtureValue_mem_convexHull {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue A μ ∈ convexHull ℝ (range A) := by
  rw [probabilityMixtureValue_eq_integral A hA μ]
  exact (convex_convexHull ℝ (range A)).integral_mem
    (isCompact_convexHull_of_isCompact (isCompact_range hA)).isClosed
    (Eventually.of_forall fun θ ↦ subset_convexHull ℝ _ (mem_range_self θ))
    (hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A))













end ReweightedNPMLE
end

/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Optimization over all probability measures is exactly the moment fiber
of the unique positive-weight fitted-vector optimum. -/
theorem solution {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hCeq : C = convexHull ℝ (range A))
    (hCpos : C ⊆ positiveVectors n)
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (μ : ProbabilityMeasure Θ) :
    IsMaxOn univ (fun ν : ProbabilityMeasure Θ ↦ weightedLogLikelihood w (probabilityMixtureValue A ν)) μ ↔
      μ ∈ probabilityMixtureFiber A v := by
  have hC : Convex ℝ C := hCeq ▸ convex_convexHull ℝ (range A)
  have hvalC : ∀ ν : ProbabilityMeasure Θ, probabilityMixtureValue A ν ∈ C := by
    intro ν
    rw [hCeq]
    exact probabilityMixtureValue_mem_convexHull A hA ν
  constructor
  · intro hopt
    have hfitmax : IsMaxOn C (weightedLogLikelihood w) (probabilityMixtureValue A μ) := by
      refine ⟨hvalC μ, ?_⟩
      intro u hu
      obtain ⟨ν, hν⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA u (hCeq ▸ hu)
      rw [← show probabilityMixtureValue A ν = u from hν]
      exact hopt.2 ν (mem_univ ν)
    exact fittedValue_maximizer_unique hC hCpos hw hfitmax hvmax
  · intro hμ
    refine ⟨mem_univ μ, ?_⟩
    intro ν _
    change weightedLogLikelihood w (probabilityMixtureValue A ν) ≤
      weightedLogLikelihood w (probabilityMixtureValue A μ)
    rw [show probabilityMixtureValue A μ = v from hμ]
    exact hvmax.2 _ (hvalC ν)
