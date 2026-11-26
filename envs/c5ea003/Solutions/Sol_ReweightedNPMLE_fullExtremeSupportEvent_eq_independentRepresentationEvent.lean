-- Prove2me | solution 1 for ReweightedNPMLE.fullExtremeSupportEvent_eq_independentRepresentationEvent
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:03:41.774727+00:00
-- url     : https://prove2.me/submissions/c907371e-b3e5-4e2d-bce9-c16cadf45ab3

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_finiteProbabilityMeasure_extreme_of_linearIndependent
import Theorems.Thm_ReweightedNPMLE_finiteProbabilityMeasure_support
import Theorems.Thm_ReweightedNPMLE_full_probability_optimizer_extreme_iff

/-!
# Maximum support of full probability-measure extreme optimizers

The statistic is defined directly from arbitrary probability measures, not
from finite representations. The full extreme-optimizer characterization
identifies each cardinality event with the independent representation event.
Consequently its supremum is a measurable, attained maximum bounded by `n`.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (k : ℕ) :
    fullExtremeSupportEvent A vhat k = independentRepresentationEvent (range A) vhat k := by
  classical
  ext w
  constructor
  · rintro ⟨hw, μ, hext, hk⟩
    obtain ⟨m, θ, p, hp, hm, hθ, hpPos, hlin, hpval, heq⟩ :=
      (full_probability_optimizer_extreme_iff A hA hC hCpos hAC w (vhat w) hw
        (hvmax w hw) μ).mp hext
    have hmcard : (μ : Measure Θ).support.ncard = m := by
      rw [← heq, finiteProbabilityMeasure_support θ hθ p hp hpPos]
      simpa using ncard_range_of_injective hθ
    have hmk : m = k := hmcard.symm.trans hk
    rw [← hmk]
    refine ⟨hw, A ∘ θ, ?_, hlin, p, hp, hpPos, hpval⟩
    rintro a ⟨j, rfl⟩
    exact mem_range_self (θ j)
  · rintro ⟨hw, B, hB, hlin, p, hp, hpPos, hpval⟩
    have hpre : ∀ j, ∃ θ : Θ, A θ = B j := fun j ↦ hB (mem_range_self j)
    choose θ hθval using hpre
    have hcomp : A ∘ θ = B := funext hθval
    have hθ : Function.Injective θ := by
      intro j l hjl
      apply hlin.injective
      rw [← hθval j, ← hθval l, hjl]
    let μ := finiteProbabilityMeasure θ p hp
    refine ⟨hw, μ, ?_, ?_⟩
    · have hext := finiteProbabilityMeasure_extreme_of_linearIndependent A hA θ p hp
        (hcomp.symm ▸ hlin)
      simpa only [hcomp, hpval] using hext
    · change (finiteProbabilityMeasure θ p hp : Measure Θ).support.ncard = k
      rw [finiteProbabilityMeasure_support θ hθ p hp hpPos]
      simpa using ncard_range_of_injective hθ
