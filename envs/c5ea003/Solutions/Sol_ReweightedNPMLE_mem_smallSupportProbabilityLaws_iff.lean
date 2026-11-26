-- Prove2me | solution 1 for ReweightedNPMLE.mem_smallSupportProbabilityLaws_iff
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:14:21.433537+00:00
-- url     : https://prove2.me/submissions/34f2fdc1-d09f-447f-97b0-f462146e3e3f

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
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SmallSupportProbability
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_probabilityMeasure_positive_finiteRepresentation_of_finite_support

-- Inline helpers preserved from ReweightedNPMLE.FiniteProbabilityExtreme.
section
/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





theorem finiteProbabilityMeasure_ae_mem_range {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) :
    ∀ᵐ x ∂(finiteProbabilityMeasure θ p hp : Measure Θ), x ∈ range θ := by
  change ∀ᵐ x ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j)), x ∈ range θ
  rw [ae_finsetSum_measure_iff]
  intro j _
  apply Measure.ae_smul_measure
  filter_upwards [ae_eq_dirac (fun x : Θ ↦ x)] with x hx
  rw [hx]
  exact mem_range_self j





















end ReweightedNPMLE
end

/-!
# Closed sets of probability laws with bounded finite support

The at-most-`m`-atom laws form a compact set in the weak topology. Finite
atomic laws are parameterized by compact atom lists and closed simplices,
including zero masses and coincident locations.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (m : ℕ) (μ : ProbabilityMeasure Θ) :
    μ ∈ smallSupportProbabilityLaws Θ m ↔
      (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ m := by
  constructor
  · intro hμ
    obtain ⟨k, p, rfl⟩ := mem_iUnion.mp hμ
    have hsub : (finiteProbabilityLawMap (k : ℕ) p : Measure Θ).support ⊆ range p.1 :=
      Measure.support_subset_of_isClosed (finite_range p.1).isClosed
        (finiteProbabilityMeasure_ae_mem_range p.1 p.2.val p.2.property)
    have hfinite := (finite_range p.1).subset hsub
    have hrange : (range p.1).ncard ≤ (k : ℕ) := by
      simpa only [image_univ, ncard_univ, Nat.card_fin] using
        (ncard_image_le (s := (univ : Set (Fin (k : ℕ)))) (f := p.1))
    refine ⟨hfinite, ?_⟩
    exact (ncard_le_ncard hsub (finite_range p.1)).trans
      (hrange.trans (by omega))
  · rintro ⟨hfinite, hcard⟩
    obtain ⟨k, θ, p, hp, hk, _, _, _, heq⟩ :=
      probabilityMeasure_positive_finiteRepresentation_of_finite_support μ hfinite
    have hkm : k < m + 1 := by omega
    exact mem_iUnion.mpr ⟨⟨k, hkm⟩, ⟨(θ, ⟨p, hp⟩), heq⟩⟩
