-- Prove2me | solution 1 for MeasureUnitary.push_measures_equivalent_of_intertwines_continuous
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:30:04.115531+00:00
-- url     : https://prove2.me/submissions/d93af4a9-e0fd-45cc-9feb-cb91504399fa

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_MeasurePullbackMultipliers
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Theorems.Thm_MeasureUnitary_exists_faithful_L2
import Theorems.Thm_MeasureUnitary_vectorSpectralState_continuous_integral

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

-- Preserved source skeleton: MeasureUnitaryDensity
section
/-! The spectral-class measure attached to an actual L² vector, expressed
without invoking a spectral theorem. Its mass on a set is the square of the
norm of the corresponding multiplication projection. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]









theorem vectorDensityMeasure_absolutelyContinuous (f : Lp E 2 μ) : vectorDensityMeasure μ f ≪ μ :=
  withDensity_absolutelyContinuous μ _















end MeasureUnitary

end

-- Preserved source skeleton: VectorSpectralState
section
/-! Finite vector-state measures and faithful vectors in actual sigma-finite
L² spaces. These give measure-class reflection without postulating a spectral theorem. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {Ω Λ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace X]













theorem faithful_vector_density (μ : Measure Ω) (f : Lp ℂ 2 μ)
    (hf : ∀ᵐ x ∂μ, f x ≠ 0) : μ ≪ vectorDensityMeasure μ f := by
  apply withDensity_absolutelyContinuous'
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const 2).ennreal_ofReal
  · filter_upwards [hf] with x hx
    exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hx))).ne'





theorem absolutelyContinuous_push_of_faithful_state
    (μ : Measure Ω) (ν : Measure Λ) (q : Ω → X) (r : Λ → X)
    (hq : Measurable q) (hr : Measurable r)
    (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (hf : ∀ᵐ x ∂μ, f x ≠ 0)
    (heq : vectorSpectralState μ q f = vectorSpectralState ν r g) :
    μ.map q ≪ ν.map r := by
  have h1 : μ.map q ≪ vectorSpectralState μ q f :=
    (faithful_vector_density μ f hf).map hq
  rw [heq] at h1
  exact h1.trans ((vectorDensityMeasure_absolutelyContinuous ν g).map hr)



end MeasureUnitary

end

-- Preserved source skeleton: VectorContinuousState
section
/-! Genuine continuous multiplication intertwiners preserve all finite
vector-state measures and hence the maximal pushforward measure class. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {Ω Λ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]



theorem vectorSpectralState_eq_of_intertwines_continuous
    (μ : Measure Ω) (ν : Measure Λ) (q : Ω → K) (r : Λ → K)
    (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (c : C(K,ℂ)) (f : Lp ℂ 2 μ),
      U (pullbackMultiplierL2 μ q hq c f) = pullbackMultiplierL2 ν r hr c (U f))
    (f : Lp ℂ 2 μ) : vectorSpectralState μ q f = vectorSpectralState ν r (U f) := by
  have hm (c : C(K,ℂ)) : (∫ x,c x ∂vectorSpectralState μ q f) =
      ∫ x,c x ∂vectorSpectralState ν r (U f) := by
    rw [vectorSpectralState_continuous_integral μ q hq,
      vectorSpectralState_continuous_integral ν r hr, ← hU, U.inner_map_map]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro c
  let z : C(K,ℂ) := ⟨fun x => (c x : ℂ), Complex.continuous_ofReal.comp c.continuous⟩
  apply Complex.ofReal_injective
  simpa only [z, ContinuousMap.coe_mk, integral_complex_ofReal] using hm z



end MeasureUnitary

end

/-! Genuine continuous multiplication intertwiners preserve all finite
vector-state measures and hence the maximal pushforward measure class. -/
open MeasureTheory Filter Set
open scoped ENNReal
namespace MeasureUnitary
end MeasureUnitary
open MeasureUnitary
variable {Ω Λ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem solution
    (μ : Measure Ω) (ν : Measure Λ) [SigmaFinite μ] [SigmaFinite ν]
    (q : Ω → K) (r : Λ → K) (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (c : C(K,ℂ)) (f : Lp ℂ 2 μ),
      U (pullbackMultiplierL2 μ q hq c f) = pullbackMultiplierL2 ν r hr c (U f)) :
    μ.map q ≪ ν.map r ∧ ν.map r ≪ μ.map q := by
  constructor
  · obtain ⟨f,hf⟩ := exists_faithful_L2 μ
    exact absolutelyContinuous_push_of_faithful_state μ ν q r hq hr f (U f) hf
      (vectorSpectralState_eq_of_intertwines_continuous μ ν q r hq hr U hU f)
  · obtain ⟨g,hg⟩ := exists_faithful_L2 ν
    have hV (c : C(K,ℂ)) (f : Lp ℂ 2 ν) :
        U.symm (pullbackMultiplierL2 ν r hr c f) =
          pullbackMultiplierL2 μ q hq c (U.symm f) := by
      apply U.injective
      simpa using (hU c (U.symm f)).symm
    exact absolutelyContinuous_push_of_faithful_state ν μ r q hr hq g (U.symm g) hg
      (vectorSpectralState_eq_of_intertwines_continuous ν μ r q hr hq U.symm hV g)
