-- Prove2me | solution 1 for MeasureEquivalenceRestrictedPhase.induced_corner_character_mass_eq
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:45:30.195735+00:00
-- url     : https://prove2.me/submissions/dace0da0-0bc2-4d61-b511-718d664360f5

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_InducedCornerUnitary
import Definitions.Def_BenchmarkOperator20261026_L2RestrictionExtension
import Definitions.Def_BenchmarkOperator20261026_L2SpectralProjectionIntertwining
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_MeasurePullbackMultipliers
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryMultipliers
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompactMeasure
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedCornerCharacterMass
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedSpectral
import Definitions.Def_BenchmarkOperator20261026_RestrictedModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPhaseFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_SeparatingMultiplierIntertwining
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Theorems.Thm_MeasureEquivalenceInducedCorners_induced_corner_unitary_mass_eq
import Theorems.Thm_MeasureUnitary_continuous_intertwines_of_separating_family
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

-- Preserved source skeleton: InducedCornerUnitary
section
/-! Actual multiplication and group-shift unitaries on the induced L2
corner modules, and their simultaneous intertwining for equal finite mass. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceInducedCorners

open MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [SigmaFinite μ]



omit [SigmaFinite μ] in
theorem inducedPhaseUnitary_coe (A : Set Z) (f : Z → ℂ) (hf : Measurable f)
    (hnorm : ∀ z, ‖f z‖ = 1) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedPhaseUnitary μ A f hf hnorm u =ᵐ[cornerMeasure (G := G) μ A]
      (fun p => f (orbitPoint p) • u p) :=
  phaseMap_coe (cornerMeasure (G := G) μ A) (fun p => f (orbitPoint p))
    (hf.comp orbitPoint_measurable) (fun p => hnorm (orbitPoint p)) u











variable (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)



end
end MeasureEquivalenceInducedCorners

end

-- Preserved source skeleton: L2RestrictionExtension
section
/-! Actual bounded restriction and isometric zero extension for complex
L2 spaces, including their projection and adjoint identities. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)



















theorem zeroExtend_restrict (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    zeroExtend μ A hA (restrictMap μ A f) = indicatorL2 μ hA f := by
  apply Lp.ext
  have hs := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (restrict_coe μ A f)
  filter_upwards [zeroExtend_coe μ A hA (restrictMap μ A f), indicatorL2_coe μ hA f, hs]
    with x he hi hsx
  exact he.trans (hsx.trans hi.symm)







end
end MeasureEquivalenceL2Restriction

end

-- Preserved source skeleton: VectorSpectralState
section
/-! Finite vector-state measures and faithful vectors in actual sigma-finite
L² spaces. These give measure-class reflection without postulating a spectral theorem. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {Ω Λ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace X]









theorem vectorSpectralState_apply (μ : Measure Ω) (q : Ω → X) (hq : Measurable q)
    (f : Lp ℂ 2 μ) {s : Set X} (hs : MeasurableSet s) :
    vectorSpectralState μ q f s =
      ENNReal.ofReal (‖indicatorL2 μ (hs.preimage hq) f‖ ^ 2) := by
  rw [vectorSpectralState, Measure.map_apply hq hs, vectorDensityMeasure_apply]













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

-- Preserved source skeleton: L2SpectralProjectionIntertwining
section
/-! Intertwining all continuous multipliers implies intertwining all
measurable spectral projections, by equality of the actual vector-state
measures and complex polarization. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

namespace MeasureUnitary

open MeasureEquivalenceL2Restriction

noncomputable section

variable {Ω Ψ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]



theorem indicatorCLM_apply (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    indicatorCLM μ hs f = indicatorL2 μ hs f := zeroExtend_restrict μ s hs f

theorem inner_indicatorL2_self (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s)
    (f : Lp ℂ 2 μ) :
    inner ℂ (indicatorL2 μ hs f) f = (‖indicatorL2 μ hs f‖ ^ 2 : ℂ) := by
  have hin : inner ℂ (indicatorL2 μ hs f) (indicatorL2 μ hs f) =
      (‖indicatorL2 μ hs f‖ ^ 2 : ℂ) := by
    simpa only [Complex.ofReal_pow] using
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (indicatorL2 μ hs f))
  rw [← hin]
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem projections_intertwine_of_vectorSpectralState_eq
    [MeasurableSpace K] (μ : Measure Ω) (ν : Measure Ψ)
    (q : Ω → K) (r : Ψ → K) (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ f, vectorSpectralState μ q f = vectorSpectralState ν r (U f))
    (s : Set K) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    U (indicatorL2 μ (hs.preimage hq) f) = indicatorL2 ν (hs.preimage hr) (U f) := by
  let P := indicatorCLM μ (hs.preimage hq)
  let Q := indicatorCLM ν (hs.preimage hr)
  let S := U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Q.comp U.toContinuousLinearEquiv.toContinuousLinearMap)
  have hnorm (g : Lp ℂ 2 μ) : ‖P g‖ ^ 2 = ‖Q (U g)‖ ^ 2 := by
    have h := congrArg (fun M : Measure K => M s) (hU g)
    change vectorSpectralState μ q g s = vectorSpectralState ν r (U g) s at h
    rw [vectorSpectralState_apply μ q hq g hs,
      vectorSpectralState_apply ν r hr (U g) hs] at h
    have hh := (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp h
    simpa only [P, Q, indicatorCLM_apply] using hh
  have hSP : S.toLinearMap = P.toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro g
    change inner ℂ (U.symm (Q (U g))) g = inner ℂ (P g) g
    calc
      inner ℂ (U.symm (Q (U g))) g = inner ℂ (Q (U g)) (U g) := by
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          (U.inner_map_map (U.symm (Q (U g))) g).symm
      _ = (‖Q (U g)‖ ^ 2 : ℂ) := by
        simpa only [Q, indicatorCLM_apply] using inner_indicatorL2_self ν (hs.preimage hr) (U g)
      _ = (‖P g‖ ^ 2 : ℂ) := by
        simpa only [Complex.ofReal_pow] using congrArg Complex.ofReal (hnorm g).symm
      _ = inner ℂ (P g) g := by
        simpa only [P, indicatorCLM_apply] using (inner_indicatorL2_self μ (hs.preimage hq) g).symm
  have h := congrArg U (LinearMap.congr_fun hSP f)
  change U (U.symm (Q (U f))) = U (P f) at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  simpa only [P, Q, indicatorCLM_apply] using h.symm

theorem projections_intertwine_of_continuous_multipliers
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure Ω) (ν : Measure Ψ) (q : Ω → K) (r : Ψ → K)
    (hq : Measurable q) (hr : Measurable r)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (c : C(K,ℂ)) (f : Lp ℂ 2 μ),
      U (pullbackMultiplierL2 μ q hq c f) = pullbackMultiplierL2 ν r hr c (U f)) :
    ∀ (s : Set K) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      U (indicatorL2 μ (hs.preimage hq) f) = indicatorL2 ν (hs.preimage hr) (U f) :=
  projections_intertwine_of_vectorSpectralState_eq μ ν q r hq hr U
    (vectorSpectralState_eq_of_intertwines_continuous μ ν q r hq hr U hU)

end
end MeasureUnitary

end

-- Preserved source skeleton: RestrictedAction
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct



theorem rationalTotal_eq_sum (q : ℕ →₀ ℚ) :
    rationalTotal q = q.sum (fun _ a => a) := by
  exact Finsupp.liftAddHom_apply _ _







theorem summable_abs_rationalRealShift (q : ℕ →₀ ℚ) :
    Summable (fun k => |rationalRealShift q k|) := by
  exact summable_of_hasFiniteSupport
    (q.hasFiniteSupport.fun_comp (g := fun a : ℚ => |(a : ℝ)|) (by simp))

theorem tsum_rationalRealShift (q : ℕ →₀ ℚ) :
    (∑' k, rationalRealShift q k) = (rationalTotal q : ℝ) := by
  rw [tsum_eq_sum (s := q.support) (fun k hk => by
    change (q k : ℝ) = 0
    rw [Finsupp.notMem_support_iff.mp hk, Rat.cast_zero])]
  rw [rationalTotal_eq_sum]
  change (∑ k ∈ q.support, (q k : ℝ)) = ((∑ k ∈ q.support, q k : ℚ) : ℝ)
  norm_cast



theorem measurePreserving_rationalTranslation (q : rationalZeroSumGroup) :
    MeasurePreserving (rationalTranslation q) restrictedProductMeasure restrictedProductMeasure := by
  constructor
  · exact measurable_id.add_const _
  · have he := map_summable_restrictedProductMeasure (rationalRealShift q)
      (summable_abs_rationalRealShift q)
    rw [tsum_rationalRealShift, show rationalTotal (q : ℕ →₀ ℚ) = 0 from q.property,
      Rat.cast_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] at he
    exact he





end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedSpectralClass
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid

theorem characterFamily_injective :
    Function.Injective (fun k : CompactSequences => fun i : CharacterIndex => character i k) := by
  intro k l he
  funext n
  apply Subtype.ext
  funext q
  apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
  apply Subtype.ext
  exact congrFun he (n, q)

















end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedInducedFamily
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition











theorem rational_smul_preserving (q : RationalGroup) :
    MeasurePreserving (fun x : RealSequences => q • x)
      restrictedProductMeasure restrictedProductMeasure :=
  measurePreserving_rationalTranslation (Multiplicative.toAdd q)



















end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedInducedSpectral
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners











theorem inducedObservable_measurable (k : CompactSequences) : Measurable (inducedObservable k) :=
  measurable_const.add (sequenceEmbedding_continuous.measurable.comp orbitPoint_measurable)







end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: SeparatingMultiplierIntertwining
section
open MeasureTheory Set Filter

noncomputable section

namespace MeasureEquivalenceRestrictedPhase





theorem characterContinuousMap_separates (x y : MeasureEquivalenceSolenoid.CompactSequences)
    (hxy : x ≠ y) : ∃ i, characterContinuousMap i x ≠ characterContinuousMap i y := by
  by_contra h
  apply hxy
  apply characterFamily_injective
  funext i
  exact not_ne_iff.mp (not_exists.mp h i)



end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedCornerCharacterMass
section
/-! Character and group-generator intertwiners of the actual restricted
product induced modules preserve the finite corner mass. -/

open MeasureTheory Filter Set
open scoped ENNReal

set_option maxHeartbeats 1500000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners

attribute [local instance] _root_.MeasureEquivalenceRestrictedPhase.instMetricSpaceCompactSequences_restrictedCornerCharacterMass

theorem pullbackCharacter_eq_cornerPhase (A : Set RealSequences)
    (k : CompactSequences) (i : CharacterIndex)
    (f : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)) :
    pullbackMultiplierL2 (cornerMeasure restrictedProductMeasure A)
      (inducedObservable k) (inducedObservable_measurable k) (characterContinuousMap i) f =
      inducedPhaseUnitary restrictedProductMeasure A (ambientPhase k i)
        (ambientPhase_measurable k i) (ambientPhase_norm k i) f := by
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe (cornerMeasure restrictedProductMeasure A)
    (inducedObservable k) (inducedObservable_measurable k) (characterContinuousMap i) f,
    inducedPhaseUnitary_coe restrictedProductMeasure A (ambientPhase k i)
      (ambientPhase_measurable k i) (ambientPhase_norm k i) f] with p hp hq
  exact hp.trans hq.symm





end MeasureEquivalenceRestrictedPhase

end

/-! Character and group-generator intertwiners of the actual restricted
product induced modules preserve the finite corner mass. -/
open MeasureTheory Filter Set
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
open MeasureEquivalenceRestrictedPhase
open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners
attribute [local instance] _root_.MeasureEquivalenceRestrictedPhase.instMetricSpaceCompactSequences_restrictedCornerCharacterMass

theorem solution (k : CompactSequences)
    (A B : Set RealSequences) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : restrictedProductMeasure A ≠ ∞) (hfinB : restrictedProductMeasure B ≠ ∞)
    (U : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure B))
    (hchar : ∀ (i : CharacterIndex)
      (u : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)),
      U (inducedPhaseUnitary restrictedProductMeasure A (ambientPhase k i)
        (ambientPhase_measurable k i) (ambientPhase_norm k i) u) =
      inducedPhaseUnitary restrictedProductMeasure B (ambientPhase k i)
        (ambientPhase_measurable k i) (ambientPhase_norm k i) (U u))
    (hshift : ∀ (g : RationalGroup)
      (u : Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure A)),
      U (inducedShiftUnitary restrictedProductMeasure A g u) =
        inducedShiftUnitary restrictedProductMeasure B g (U u)) :
    restrictedProductMeasure A = restrictedProductMeasure B := by
  have hcont := continuous_intertwines_of_separating_family
    (cornerMeasure restrictedProductMeasure A) (cornerMeasure restrictedProductMeasure B)
    (inducedObservable k) (inducedObservable k)
    (inducedObservable_measurable k) (inducedObservable_measurable k)
    characterContinuousMap characterContinuousMap_separates U
    (fun i u => by simpa only [pullbackCharacter_eq_cornerPhase] using hchar i u)
  have hproj := projections_intertwine_of_continuous_multipliers
    (cornerMeasure restrictedProductMeasure A) (cornerMeasure restrictedProductMeasure B)
    (inducedObservable k) (inducedObservable k)
    (inducedObservable_measurable k) (inducedObservable_measurable k) U hcont
  apply induced_corner_unitary_mass_eq restrictedProductMeasure rational_smul_preserving
    A B hA hB hfinA hfinB U _ hshift
  intro s hs u
  let F : RealSequences → CompactSequences := fun x => k + sequenceEmbedding x
  have hF : MeasurableEmbedding F :=
    (MeasurableEquiv.addLeft k).measurableEmbedding.comp sequenceEmbedding_measurableEmbedding
  have hFs : MeasurableSet (F '' s) := hF.measurableSet_image.mpr hs
  have hpre : inducedObservable k ⁻¹' (F '' s) = orbitPoint ⁻¹' s := by
    change (F ∘ orbitPoint) ⁻¹' (F '' s) = _
    rw [Set.preimage_comp, Set.preimage_image_eq _ hF.injective]
  have h := hproj (F '' s) hFs u
  simpa only [hpre] using h
