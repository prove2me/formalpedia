-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.exists_base_event_of_ae_fiber_const
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:34:51.145165+00:00
-- url     : https://prove2.me/submissions/b0f3f31c-4c6b-43a3-825d-a4cb8c2adcd8

import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Rat

set_option autoImplicit false

namespace MeasurableEquiv
end MeasurableEquiv
namespace MeasureEquivalenceCompactAveraging
end MeasureEquivalenceCompactAveraging
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
namespace MeasureEquivalenceDensityGraph
end MeasureEquivalenceDensityGraph
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
namespace MeasureEquivalenceEquidecomposition.greedyRemainder
end MeasureEquivalenceEquidecomposition.greedyRemainder
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
namespace MeasureEquivalenceInvariantGraph
end MeasureEquivalenceInvariantGraph
namespace MeasureEquivalenceInverseAC
end MeasureEquivalenceInverseAC
namespace MeasureEquivalenceL2Coefficients
end MeasureEquivalenceL2Coefficients
namespace MeasureEquivalenceL2Restriction
end MeasureEquivalenceL2Restriction
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
namespace MeasureEquivalenceMarkov.kernelIterate
end MeasureEquivalenceMarkov.kernelIterate
namespace MeasureEquivalenceRNGraph
end MeasureEquivalenceRNGraph
namespace MeasureEquivalenceRNPresentation
end MeasureEquivalenceRNPresentation
namespace MeasureEquivalenceResearch
end MeasureEquivalenceResearch
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages
end MeasureEquivalenceRestrictedProduct.CompatibleStages
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
end MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
namespace MeasureEquivalenceRestrictedRoots
end MeasureEquivalenceRestrictedRoots
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
namespace MeasureEquivalenceSharedDensity
end MeasureEquivalenceSharedDensity
namespace MeasureEquivalenceSolenoid
end MeasureEquivalenceSolenoid
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
namespace MeasureUnitary
end MeasureUnitary
namespace MeasureUnitary.FiniteBorelSection
end MeasureUnitary.FiniteBorelSection
namespace OperatorCoding
end OperatorCoding
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace lp
end lp

open MeasureTheory Set Filter
open scoped ENNReal
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν ρ : Measure β) [SFinite μ] [SFinite ν] [IsProbabilityMeasure ρ]
    (hρ : ρ ≪ ν) (E : Set (α × β)) (hE : MeasurableSet E)
    (hc : ∀ᵐ x ∂μ, EventuallyConst (Prod.mk x ⁻¹' E) (ae ν)) :
    ∃ A : Set α, MeasurableSet A ∧ E =ᵐ[μ.prod ν] Prod.fst ⁻¹' A := by
  let A : Set α := {x | ρ (Prod.mk x ⁻¹' E) = 1}
  have hA : MeasurableSet A :=
    (measurable_measure_prodMk_left hE) (measurableSet_singleton 1)
  refine ⟨A, hA, ?_⟩
  change ∀ᵐ z ∂μ.prod ν, E z = (z.1 ∈ A)
  simp only [eq_iff_iff]
  apply (Measure.ae_prod_iff_ae_ae (hE.iff (measurable_fst hA))).2
  filter_upwards [hc] with x hx
  rcases eventuallyConst_set.mp hx with hx | hx
  · have hp : ρ (Prod.mk x ⁻¹' E) = 1 := by
      exact (mem_ae_iff_prob_eq_one (measurable_prodMk_left hE)).mp (hρ.ae_le hx)
    filter_upwards [hx] with y hy
    exact ⟨fun _ => hp, fun _ => hy⟩
  · have hp : ρ (Prod.mk x ⁻¹' E) = 0 := by
      have hz := mem_ae_iff.mp (hρ.ae_le hx)
      have he : {y | y ∉ Prod.mk x ⁻¹' E}ᶜ = Prod.mk x ⁻¹' E := by ext y; simp
      rw [he] at hz
      exact hz
    have hn : x ∉ A := by change ρ (Prod.mk x ⁻¹' E) ≠ 1; rw [hp]; exact zero_ne_one
    filter_upwards [hx] with y hy
    exact ⟨fun he => (hy he).elim, fun ha => (hn ha).elim⟩
