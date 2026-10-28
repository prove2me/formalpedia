-- Prove2me | solution 1 for BenchmarkComparisons.cyclic_representations_borelReduces_measure
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:01:21.869456+00:00
-- url     : https://prove2.me/submissions/bd9046ee-057d-4284-b86c-8016e5be6fa0

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_L2CountCoefficients
import Definitions.Def_BenchmarkOperator20261026_L2CountInjections
import Definitions.Def_BenchmarkOperator20261026_L2LocalizedOperators
import Definitions.Def_BenchmarkOperator20261026_L2ModuleCommutant
import Definitions.Def_BenchmarkOperator20261026_L2RestrictionExtension
import Definitions.Def_BenchmarkOperator20261026_L2SpectralProjectionIntertwining
import Definitions.Def_BenchmarkOperator20261026_MeasurePullbackMultipliers
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryMultipliers
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryRN
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Definitions.Def_BenchmarkOperator20261026_PiecewiseMeasureTransport
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Definitions.Def_BenchmarkRelations
import Init
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false

namespace BenchmarkComparisons
end BenchmarkComparisons
namespace ContinuousMap
end ContinuousMap
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
namespace OperatorCoding.greedyCyclicGenerator
end OperatorCoding.greedyCyclicGenerator
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace SpectralDomination
end SpectralDomination
namespace lp
end lp


/- Preserved source skeleton: OperatorTargets -/
section Source0
/-!
Exact target propositions for Theorems 1.3 and 1.4 of MeasureEquivalence.tex.
These are definitions of the outstanding goals, not proofs of those goals.
The operator topology is strong convergence on vectors. Representations are
all group homomorphisms to the genuine strong unitary group.
-/

open MeasureTheory

namespace OperatorCoding

noncomputable section




abbrev UnitaryRepresentation (Γ : Type*) [Group Γ] := Γ →* StrongUnitary CanonicalHilbert





abbrev unitaryRepresentationTopology (Γ : Type*) [Group Γ] :
    TopologicalSpace (UnitaryRepresentation Γ) :=
  TopologicalSpace.induced
    (fun ρ : UnitaryRepresentation Γ => fun g : Γ => ρ g) inferInstance

abbrev unitaryRepresentationBorel (Γ : Type*) [Group Γ] :
    MeasurableSpace (UnitaryRepresentation Γ) :=
  @borel (UnitaryRepresentation Γ) (unitaryRepresentationTopology Γ)



def UnitaryRepresentationEquivalent {Γ : Type*} [Group Γ]
    (ρ σ : UnitaryRepresentation Γ) : Prop :=
  ∃ u : StrongUnitary CanonicalHilbert, ∀ g, u * ρ g * u⁻¹ = σ g



def BorelBireducibleWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  BorelReducesWith mX mY E F ∧ BorelReducesWith mY mX F E



theorem borelReducesWith_trans {X Y Z : Type*}
    {mX : MeasurableSpace X} {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z}
    {E : X → X → Prop} {F : Y → Y → Prop} {G : Z → Z → Prop}
    (hEF : BorelReducesWith mX mY E F) (hFG : BorelReducesWith mY mZ F G) :
    BorelReducesWith mX mZ E G := by
  obtain ⟨f, hf, hE⟩ := hEF
  obtain ⟨g, hg, hF⟩ := hFG
  exact ⟨g ∘ f, @Measurable.comp X Y Z mX mY mZ g f hg hf,
    fun x y => (hE x y).trans (hF (f x) (f y))⟩





end
end OperatorCoding

end Source0

/- Preserved source skeleton: MeasureGramSchmidtBorel -/
section Source1
/-! Borel Gram–Schmidt and Borel removal of its zero vectors.
These are fixed-fiber results; a parameter-dependent L² trivialization still
requires a measurable dense fundamental family. -/

open MeasureTheory InnerProductSpace Set Finset

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_gramSchmidt (f : S → ℕ → E)
    (hf : ∀ n, Measurable (fun s => f s n)) (n : ℕ) :
    Measurable (fun s => gramSchmidt ℂ (f s) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have heq : (fun s => gramSchmidt ℂ (f s) n) = fun s => f s n -
        ∑ i ∈ Finset.Iio n,
          (inner ℂ (gramSchmidt ℂ (f s) i) (f s n) /
            ((‖gramSchmidt ℂ (f s) i‖ ^ 2 : ℝ) : ℂ)) • gramSchmidt ℂ (f s) i := by
      funext s
      rw [gramSchmidt_def]
      simp only [Submodule.starProjection_singleton]
      rfl
    rw [heq]
    apply (hf n).sub
    apply Finset.measurable_sum
    intro i hi
    have hg := ih i (Finset.mem_Iio.mp hi)
    have hden : Measurable (fun s => ((‖gramSchmidt ℂ (f s) i‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hg.norm.pow_const 2)
    exact ((hg.inner (hf n)).div hden).smul hg



theorem measurable_nat_count (p : S → ℕ → Prop) [∀ s, DecidablePred (p s)]
    (hp : ∀ n, MeasurableSet {s | p s n}) (n : ℕ) :
    Measurable (fun s => Nat.count (p s) n) := by
  induction n with
  | zero => simpa only [Nat.count_zero] using (measurable_const : Measurable (fun _ : S => (0 : ℕ)))
  | succ n ih =>
    simp_rw [Nat.count_succ]
    exact ih.add (Measurable.ite (hp n) measurable_const measurable_const)



















end MeasureUnitary

end Source1

/- Preserved source skeleton: MeasureUnitaryMultipliers -/
section Source2
/-! Genuine multiplication unitaries in complex L², and their natural
intertwining by the square-root Radon–Nikodym unitary. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (c : α → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)

include hc hnorm















variable (ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]

theorem rnWeightedEquiv_intertwines_phase (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E 2 μ) :
    rnWeightedEquiv μ ν hμν hνμ (phaseEquiv μ c hc hnorm f) =
      phaseEquiv ν c hc hnorm (rnWeightedEquiv μ ν hμν hνμ f) := by
  change rnWeightedMap μ ν hμν hνμ (phaseMap μ c hc hnorm f) =
    phaseMap ν c hc hnorm (rnWeightedMap μ ν hμν hνμ f)
  apply Lp.ext
  filter_upwards [rnWeightedMap_coe μ ν hμν hνμ (phaseMap μ c hc hnorm f),
    hνμ.ae_eq (phaseMap_coe μ c hc hnorm f),
    phaseMap_coe ν c hc hnorm (rnWeightedMap μ ν hμν hνμ f),
    rnWeightedMap_coe μ ν hμν hνμ f] with x hleft hphase hright hRN
  rw [hleft, hphase, hright, hRN]
  change rnWeight μ ν x • (c x • f x) = c x • (rnWeight μ ν x • f x)
  exact smul_comm _ _ _

end MeasureUnitary

end Source2

/- Preserved source skeleton: OperatorStrongExponential -/
section Source3
/-! Strong continuity of the operator exponential on uniformly bounded
families. The proof uses continuous powers and the factorial majorant. -/

open Filter Topology ContinuousLinearMap

namespace OperatorCoding

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace α]

theorem strongOperator_continuous_action {A : α → H →L[ℂ] H} {C : ℝ}
    (hA : ∀ v : H, Continuous (fun a => A a v)) (hbound : ∀ a, ‖A a‖ ≤ C)
    {x : α → H} (hx : Continuous x) : Continuous (fun a => A a (x a)) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ : Tendsto (fun b => C * dist (x b) (x a)) (𝓝 a) (𝓝 0) := by
    simpa using ((continuous_const (y := C)).mul (hx.dist (continuous_const (y := x a)))).tendsto a
  have h₂ : Tendsto (fun b => dist (A b (x a)) (A a (x a))) (𝓝 a) (𝓝 0) := by
    simpa using ((hA (x a)).dist (continuous_const (y := A a (x a)))).tendsto a
  apply squeeze_zero (fun b => dist_nonneg) (fun b => ?_) (by simpa using h₁.add h₂)
  calc
    dist (A b (x b)) (A a (x a)) ≤
        dist (A b (x b)) (A b (x a)) + dist (A b (x a)) (A a (x a)) := dist_triangle _ _ _
    _ ≤ C * dist (x b) (x a) + dist (A b (x a)) (A a (x a)) := by
      exact add_le_add (((A b).dist_le_opNorm (x b) (x a)).trans
        (mul_le_mul_of_nonneg_right (hbound b) dist_nonneg)) le_rfl











end OperatorCoding

end Source3

/- Preserved source skeleton: MeasureContinuousMultipliers -/
section Source4
/-! The genuine continuous-function multiplication representation on
Hilbert-valued L², including its bounded linear and star-algebra structures. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α]
  (μ : Measure α) [IsFiniteMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def continuousMultiplierL2 : C(α, ℂ) →L[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) :=
  ((ContinuousLinearMap.lsmul ℂ ℂ (E := E)).holderL μ ∞ 2 2).comp
    (ContinuousMap.toLp ∞ μ ℂ)

theorem continuousMultiplierL2_coe (g : C(α, ℂ)) (f : Lp E 2 μ) :
    continuousMultiplierL2 μ g f =ᵐ[μ] fun x => g x • f x := by
  have hh := (ContinuousLinearMap.lsmul ℂ ℂ (E := E)).coeFn_holder (r := 2)
    (ContinuousMap.toLp ∞ μ ℂ g) f
  filter_upwards [hh, ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) μ g] with x hh hg
  exact hh.trans (by rw [hg]; rfl)











theorem continuousMultiplierL2_phase (c : C(α, ℂ)) (hnorm : ∀ x, ‖c x‖ = 1) (f : Lp E 2 μ) :
    continuousMultiplierL2 μ c f = phaseEquiv μ c c.continuous.measurable hnorm f := by
  apply Lp.ext
  exact (continuousMultiplierL2_coe μ c f).trans (phaseMap_coe μ c c.continuous.measurable hnorm f).symm

end

end MeasureUnitary

end Source4

/- Preserved source skeleton: OperatorCyclicRepresentation -/
section Source5
/-! Representations of the infinite cyclic group are exactly one unitary,
with the pointwise strong topology and exact conjugacy preserved. -/

namespace OperatorCoding

section General

variable {G : Type*} [Group G]

def ElementConjugate (u v : G) : Prop := ∃ w : G, w*u*w⁻¹ = v

theorem cyclic_conjugate_iff (u v : G) :
    (∃ w : G, ∀ n : Multiplicative ℤ,
      w * zpowersHom G u n * w⁻¹ = zpowersHom G v n) ↔ ElementConjugate u v := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨w,by simpa using hw (Multiplicative.ofAdd 1)⟩
  · rintro ⟨w,hw⟩
    refine ⟨w,fun n => ?_⟩
    simp only [zpowersHom_apply]
    rw [← conj_zpow, hw]

variable [TopologicalSpace G] [IsTopologicalGroup G]

instance cyclicRepresentationTopology : TopologicalSpace (Multiplicative ℤ →* G) :=
  TopologicalSpace.induced
    (fun ρ : Multiplicative ℤ →* G => (ρ : Multiplicative ℤ → G)) inferInstance

theorem continuous_zpowersHom : Continuous (zpowersHom G) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun n => continuous_id.zpow n.toAdd)

theorem continuous_cyclic_generator :
    Continuous (fun ρ : Multiplicative ℤ →* G => ρ (Multiplicative.ofAdd 1)) :=
  (continuous_apply (Multiplicative.ofAdd 1)).comp continuous_induced_dom



end General

theorem cyclicRepresentations_borelBireducible_unitaries :
    BorelBireducibleWith (unitaryRepresentationBorel (Multiplicative ℤ))
      (borel (StrongUnitary CanonicalHilbert))
      UnitaryRepresentationEquivalent ElementConjugate := by
  constructor
  · refine ⟨(zpowersHom (StrongUnitary CanonicalHilbert)).symm,
      continuous_cyclic_generator.borel_measurable,fun ρ σ => ?_⟩
    simpa only [Equiv.apply_symm_apply] using
      cyclic_conjugate_iff ((zpowersHom _).symm ρ) ((zpowersHom _).symm σ)
  · exact ⟨zpowersHom _, continuous_zpowersHom.borel_measurable,
      fun u v => (cyclic_conjugate_iff u v).symm⟩

end OperatorCoding

end Source5

/- Preserved source skeleton: SeparatingMultiplierIntertwining -/
section Source6
open MeasureTheory Set Filter

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

theorem starAlgHom_eq_of_separating_family
    {K B ι : Type*} [TopologicalSpace K] [CompactSpace K]
    [Semiring B] [StarRing B] [Algebra ℂ B]
    [TopologicalSpace B] [T2Space B]
    (φ ψ : C(K, ℂ) →⋆ₐ[ℂ] B) (hφ : Continuous φ) (hψ : Continuous ψ)
    (c : ι → C(K, ℂ))
    (hsep : ∀ x y : K, x ≠ y → ∃ i, c i x ≠ c i y)
    (heq : ∀ i, φ (c i) = ψ (c i)) : φ = ψ := by
  let A := StarAlgHom.equalizer φ ψ
  have hclosed : IsClosed (A : Set C(K, ℂ)) := isClosed_eq hφ hψ
  have hAsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    exact ⟨c i, ⟨c i, heq i, rfl⟩, hi⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hAsep
  apply DFunLike.ext
  intro f
  have hf : f ∈ closure (A : Set C(K, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]
    trivial
  exact hclosed.closure_subset hf







end MeasureEquivalenceRestrictedPhase

end
end Source6

/- Preserved source skeleton: MeasureCharacterIntertwining -/
section Source7
/-! Genuine unitary intertwiners of a separating continuous family
intertwine every pulled-back continuous multiplier. The two underlying
measure spaces may be arbitrary and have different Hilbert coefficient fibers. -/

open MeasureTheory

namespace MeasureUnitary

noncomputable section

variable {Ω Ψ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [SecondCountableTopology K]
  (μ : Measure Ω) (ν : Measure Ψ) (q : Ω → K) (r : Ψ → K) (hq : Measurable q) (hr : Measurable r)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem pullbackMultiplierL2_phase (c : C(K, ℂ)) (hc : ∀ x, ‖c x‖ = 1) (f : Lp E 2 μ) :
    pullbackMultiplierL2 μ q hq c f = phaseEquiv μ (fun x => c (q x))
      (c.continuous.measurable.comp hq) (fun x => hc (q x)) f := by
  apply Lp.ext
  exact (pullbackMultiplierL2_coe μ q hq c f).trans
    (phaseMap_coe μ (fun x => c (q x)) (c.continuous.measurable.comp hq) (fun x => hc (q x)) f).symm

theorem continuous_intertwines_of_separating_family {I : Type*}
    (c : I → C(K, ℂ)) (hsep : ∀ x y : K, x ≠ y → ∃ i, c i x ≠ c i y)
    (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp F 2 ν)
    (hU : ∀ i f, U (pullbackMultiplierL2 μ q hq (c i) f) =
      pullbackMultiplierL2 ν r hr (c i) (U f)) :
    ∀ g f, U (pullbackMultiplierL2 μ q hq g f) = pullbackMultiplierL2 ν r hr g (U f) := by
  let φ : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) :=
    (U.conjStarAlgEquiv : (Lp E 2 μ →L[ℂ] Lp E 2 μ) →⋆ₐ[ℂ]
      (Lp F 2 ν →L[ℂ] Lp F 2 ν)).comp (pullbackMultiplierStarAlgHom (E := E) μ q hq)
  let ψ : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) := pullbackMultiplierStarAlgHom ν r hr
  have heq : φ = ψ := by
    apply MeasureEquivalenceRestrictedPhase.starAlgHom_eq_of_separating_family φ ψ
      (U.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp (pullbackMultiplierL2 μ q hq).continuous)
      (pullbackMultiplierL2 ν r hr).continuous c hsep
    intro i
    apply ContinuousLinearMap.ext
    intro f
    change U (pullbackMultiplierL2 μ q hq (c i) (U.symm f)) = pullbackMultiplierL2 ν r hr (c i) f
    simpa using hU i (U.symm f)
  intro g f
  have h := congrArg (fun H : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) => H g (U f)) heq
  change U (pullbackMultiplierL2 μ q hq g (U.symm (U f))) = pullbackMultiplierL2 ν r hr g (U f) at h
  simpa using h

theorem continuous_intertwines_of_separating_phases {I : Type*}
    (c : I → C(K, ℂ)) (hc : ∀ i x, ‖c i x‖ = 1)
    (hsep : ∀ x y : K, x ≠ y → ∃ i, c i x ≠ c i y)
    (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp F 2 ν)
    (hU : ∀ i f, U (phaseEquiv μ (fun x => c i (q x))
        ((c i).continuous.measurable.comp hq) (fun x => hc i (q x)) f) =
      phaseEquiv ν (fun x => c i (r x)) ((c i).continuous.measurable.comp hr)
        (fun x => hc i (r x)) (U f)) :
    ∀ g f, U (pullbackMultiplierL2 μ q hq g f) = pullbackMultiplierL2 ν r hr g (U f) := by
  apply continuous_intertwines_of_separating_family μ ν q r hq hr c hsep U
  intro i f
  simpa only [pullbackMultiplierL2_phase _ _ _ _ (hc i)] using hU i f

end

end MeasureUnitary

end Source7

/- Preserved source skeleton: L2ModuleCommutant -/
section Source8
/-! A bounded operator commuting with measurable multiplication
projections has an essentially bounded multiplier as its value at one.
This is a concrete L² module lemma for the finite-corner construction. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]









theorem constantVectorL2_eq_smul_one (c : ℂ) :
    constantVectorL2 μ c = c • constantOneL2 μ := by
  apply Lp.ext
  filter_upwards [constantVectorL2_coe μ c, constantOneL2_coe μ,
    Lp.coeFn_smul c (constantOneL2 μ)] with x hc h1 hsmul
  rw [hc, hsmul]
  simp [h1]

theorem indicatorConstLp_eq_indicator_one {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : ℂ) :
    indicatorConstLp 2 hs hμs c = indicatorL2 μ hs (constantVectorL2 μ c) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c),
    indicatorL2_coe μ hs (constantVectorL2 μ c), constantVectorL2_coe μ c]
      with x hleft hright hc
  rw [hleft, hright]
  by_cases hx : x ∈ s <;> simp [hx, hc]

theorem projectionCommutant_determined_by_one (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hS : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      S (indicatorL2 μ hs f) = indicatorL2 μ hs (S f))
    (hone : T (constantOneL2 μ) = S (constantOneL2 μ)) : T = S := by
  have hfun : (T : Lp ℂ 2 μ → Lp ℂ 2 μ) = S := by
    apply Continuous.ext_on (Lp.simpleFunc.dense (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
      T.continuous S.continuous
    intro f hf
    lift f to Lp.simpleFunc ℂ 2 μ using hf
    induction f using Lp.simpleFunc.induction (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) with
    | @indicatorConst c s hs hμs =>
      dsimp only [Lp.simpleFunc.coe_indicatorConst]
      rw [indicatorConstLp_eq_indicator_one μ hs hμs.ne c, hT, hS]
      have hc : T (constantVectorL2 μ c) = S (constantVectorL2 μ c) := by
        rw [constantVectorL2_eq_smul_one, map_smul, map_smul, hone]
      rw [hc]
    | @add f g hf hg _ ihf ihg =>
      change T ((f.toLp hf : Lp ℂ 2 μ) + (g.toLp hg : Lp ℂ 2 μ)) =
        S ((f.toLp hf : Lp ℂ 2 μ) + (g.toLp hg : Lp ℂ 2 μ))
      rw [map_add, map_add, ihf, ihg]
  exact DFunLike.coe_injective hfun



omit [IsFiniteMeasure μ] in
theorem boundedMultiplierL2_coe (b : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    boundedMultiplierL2 μ b f =ᵐ[μ] fun x => b x * f x := by
  exact (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) b f

omit [IsFiniteMeasure μ] in
theorem boundedMultiplierL2_indicator (b : Lp ℂ ∞ μ) {s : Set α} (hs : MeasurableSet s)
    (f : Lp ℂ 2 μ) :
    boundedMultiplierL2 μ b (indicatorL2 μ hs f) =
      indicatorL2 μ hs (boundedMultiplierL2 μ b f) := by
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ b (indicatorL2 μ hs f),
    indicatorL2_coe μ hs f, indicatorL2_coe μ hs (boundedMultiplierL2 μ b f),
    boundedMultiplierL2_coe μ b f] with x hm hi ho hf
  rw [hm, hi, ho]
  by_cases hx : x ∈ s <;> simp [hx, hf]



theorem projectionCommutantSymbol_coe (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    projectionCommutantSymbol μ T hT =ᵐ[μ] fun x => T (constantOneL2 μ) x :=
  (projectionCommutant_value_memLp_top μ T hT).coeFn_toLp

theorem projectionCommutant_eq_multiplier (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    T = boundedMultiplierL2 μ (projectionCommutantSymbol μ T hT) := by
  apply projectionCommutant_determined_by_one μ T _ hT
    (fun _ hs f => boundedMultiplierL2_indicator μ _ hs f)
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT)
      (constantOneL2 μ), projectionCommutantSymbol_coe μ T hT, constantOneL2_coe μ]
    with x hm hs h1
  rw [hm, hs, h1, mul_one]

end MeasureUnitary

end Source8

/- Preserved source skeleton: VectorSpectralState -/
section Source9
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











theorem vectorSpectralState_integral (μ : Measure Ω) (q : Ω → X) (hq : Measurable q)
    (f : Lp ℂ 2 μ) (c : X → ℂ) (hc : Measurable c) (b : Lp ℂ ∞ μ)
    (hb : b =ᵐ[μ] fun x => c (q x)) :
    (∫ x, c x ∂vectorSpectralState μ q f) =
      inner ℂ f (boundedMultiplierL2 μ b f) := by
  rw [vectorSpectralState, integral_map hq.aemeasurable hc.aestronglyMeasurable,
    vectorDensityMeasure, integral_withDensity_eq_integral_toReal_smul₀
      (((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const 2).ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMultiplierL2_coe μ b f,hb] with x hmul hbx
  rw [hmul,hbx]
  change (ENNReal.ofReal (‖f x‖ ^ 2)).toReal • c (q x) =
    inner ℂ (f x) (c (q x) • f x)
  rw [ENNReal.toReal_ofReal (sq_nonneg _), inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp only [Complex.real_smul, mul_comm, Complex.ofReal_pow]
  rfl

end MeasureUnitary

end Source9

/- Preserved source skeleton: VectorContinuousState -/
section Source10
/-! Genuine continuous multiplication intertwiners preserve all finite
vector-state measures and hence the maximal pushforward measure class. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {Ω Λ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem vectorSpectralState_continuous_integral (μ : Measure Ω) (q : Ω → K)
    (hq : Measurable q) (f : Lp ℂ 2 μ) (c : C(K,ℂ)) :
    (∫ x, c x ∂vectorSpectralState μ q f) =
      inner ℂ f (pullbackMultiplierL2 μ q hq c f) := by
  have heq : boundedMultiplierL2 μ (pullbackContinuousSymbol μ q hq c) =
      pullbackMultiplierL2 (E := ℂ) μ q hq c := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [boundedMultiplierL2_coe μ (pullbackContinuousSymbol μ q hq c) f,
      pullbackContinuousSymbol_coe μ q hq c, pullbackMultiplierL2_coe μ q hq c f]
      with x hleft hs hright
    rw [hleft,hs,hright]
    rfl
  rw [← heq]
  exact vectorSpectralState_integral μ q hq f c c.continuous.measurable
    (pullbackContinuousSymbol μ q hq c) (pullbackContinuousSymbol_coe μ q hq c)

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

end Source10

/- Preserved source skeleton: L2MatrixProjection -/
section Source11
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceL2Coefficients

open MeasureUnitary

variable {X Y D Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D] [MeasurableSpace Z]
  (μ : Measure X) [SigmaFinite μ]

theorem coefficient_indicator (q : X × D → Z) (hq : Measurable q)
    (s : Set Z) (hs : MeasurableSet s) (d : D)
    (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    coefficient μ d (indicatorL2 (μ.prod Measure.count) (hq hs) u) =
      indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) (coefficient μ d u) := by
  apply Lp.ext
  filter_upwards [coefficient_coe μ d (indicatorL2 (μ.prod Measure.count) (hq hs) u),
    ae_slice_of_ae μ (indicatorL2_coe (μ.prod Measure.count) (hq hs) u) d,
    indicatorL2_coe μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) (coefficient μ d u),
    coefficient_coe μ d u] with x hc hi ho hu
  rw [hc, hi, ho]
  by_cases hx : q (x,d) ∈ s <;> simp [hx, hu]

theorem injection_indicator (q : X × D → Z) (hq : Measurable q)
    (s : Set Z) (hs : MeasurableSet s) (d : D) (u : Lp ℂ 2 μ) :
    injection μ d (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u) =
      indicatorL2 (μ.prod Measure.count) (hq hs) (injection μ d u) := by
  classical
  apply Lp.ext
  filter_upwards [injection_coe μ d
      (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u),
    indicatorL2_coe (μ.prod Measure.count) (hq hs) (injection μ d u), injection_coe μ d u,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (Measure.count : Measure D))).ae
      (indicatorL2_coe μ ((hq.comp (measurable_id.prodMk (measurable_const (a := d)))) hs) u)]
      with p hleft hright hinj hbase
  rw [hleft, hright]
  simp only [Set.indicator_apply]
  rw [hinj]
  by_cases hd : p.2 = d
  · have hp' : p = (p.1, d) := Prod.ext rfl hd
    rw [hp'] at *
    simp only [injectionFun, if_pos rfl]
    rw [hbase]
    by_cases hp : q (p.1, d) ∈ s
    · simp [hp]
    · simp [hp]
  · by_cases hp : q p ∈ s <;> simp [injectionFun, hd, hp]

variable (ν : Measure Y) [SigmaFinite ν]

/-- Matrix coefficients of an actual intertwiner satisfy the twisted
measurable-projection relation on their source and target slices. -/
theorem matrixCoefficient_intertwines_projections
    (q : X × D → Z) (r : Y × D → Z) (hq : Measurable q) (hr : Measurable r)
    (T : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D)))
    (hT : ∀ (s : Set Z) (hs : MeasurableSet s)
      (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))),
      T (indicatorL2 (μ.prod Measure.count) (hq hs) u) =
        indicatorL2 (ν.prod Measure.count) (hr hs) (T u))
    (s : Set Z) (hs : MeasurableSet s) (d e : D) (u : Lp ℂ 2 μ) :
    matrixCoefficient μ ν T d e
      (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := e)))) hs) u) =
        indicatorL2 ν ((hr.comp (measurable_id.prodMk (measurable_const (a := d)))) hs)
          (matrixCoefficient μ ν T d e u) := by
  change coefficient ν d (T (injection μ e
    (indicatorL2 μ ((hq.comp (measurable_id.prodMk (measurable_const (a := e)))) hs) u))) =
      indicatorL2 ν ((hr.comp (measurable_id.prodMk (measurable_const (a := d)))) hs)
        (coefficient ν d (T (injection μ e u)))
  rw [injection_indicator μ q hq s hs e u, hT s hs, coefficient_indicator ν r hr s hs d]

end MeasureEquivalenceL2Coefficients

end
end Source11

/- Preserved source skeleton: L2CountAdjoints -/
section Source12
/-! Actual adjoint identities for the coordinate injections and
coefficients, and adjoint transposition of genuine operator matrices. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureEquivalenceL2Coefficients

open MeasureUnitary

variable {X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (μ : Measure X) [SigmaFinite μ]

theorem inner_injection_coefficient (d : D) (f : Lp ℂ 2 μ)
    (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    inner ℂ (injection μ d f) u = inner ℂ f (coefficient μ d u) := by
  classical
  have hI := L2.integrable_inner (𝕜 := ℂ) (injection μ d f) u
  have hterm (i : D) :
      (∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ) =
        if i = d then inner ℂ f (coefficient μ d u) else 0 := by
    by_cases hi : i = d
    · subst i
      rw [if_pos rfl, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ae_slice_of_ae μ (injection_coe μ d f) d,
        coefficient_coe μ d u] with x hinj hc
      rw [hinj, hc]
      simp [injectionFun]
    · rw [if_neg hi]
      calc
        (∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ) = ∫ _ : X, (0 : ℂ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_slice_of_ae μ (injection_coe μ d f) i] with x hinj
          rw [hinj]
          simp [injectionFun, hi]
        _ = 0 := integral_zero _ _
  calc
    inner ℂ (injection μ d f) u =
        ∑' i : D, ∫ x, inner ℂ (injection μ d f (x,i)) (u (x,i)) ∂μ := by
      rw [L2.inner_def, integral_prod_symm _ hI, integral_countable hI.integral_prod_right]
      simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    _ = ∑' i : D, if i = d then inner ℂ f (coefficient μ d u) else 0 := tsum_congr hterm
    _ = inner ℂ f (coefficient μ d u) := by simp

theorem coefficient_adjoint (d : D) :
    (coefficientCLM μ d).adjoint = (injectionLI μ d).toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact fun f u => inner_injection_coefficient μ d f u

theorem injection_adjoint (d : D) :
    (injectionLI μ d).toContinuousLinearMap.adjoint = coefficientCLM μ d := by
  rw [← coefficient_adjoint, ContinuousLinearMap.adjoint_adjoint]

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]

/-- The genuine operator coefficient matrix transposes under adjoint. -/
theorem matrixCoefficient_adjoint
    (T : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (d e : D) :
    (matrixCoefficient μ ν T d e).adjoint = matrixCoefficient ν μ T.adjoint e d := by
  simp only [matrixCoefficient, ContinuousLinearMap.adjoint_comp, injection_adjoint,
    coefficient_adjoint, ContinuousLinearMap.comp_assoc]



end MeasureEquivalenceL2Coefficients

end Source12

/- Preserved source skeleton: L2RestrictionExtension -/
section Source13
/-! Actual bounded restriction and isometric zero extension for complex
L2 spaces, including their projection and adjoint identities. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

















theorem restrict_zeroExtend (A : Set X) (hA : MeasurableSet A)
    (f : Lp ℂ 2 (μ.restrict A)) : restrictMap μ A (zeroExtend μ A hA f) = f := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (zeroExtend μ A hA f),
    ae_restrict_of_ae (zeroExtend_coe μ A hA f), ae_restrict_mem hA] with x hr he hx
  rw [hr, he]
  simp only [Set.indicator_of_mem hx]

theorem zeroExtend_restrict (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    zeroExtend μ A hA (restrictMap μ A f) = indicatorL2 μ hA f := by
  apply Lp.ext
  have hs := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (restrict_coe μ A f)
  filter_upwards [zeroExtend_coe μ A hA (restrictMap μ A f), indicatorL2_coe μ hA f, hs]
    with x he hi hsx
  exact he.trans (hsx.trans hi.symm)

theorem inner_zeroExtend_restrict (A : Set X) (hA : MeasurableSet A)
    (f : Lp ℂ 2 (μ.restrict A)) (g : Lp ℂ 2 μ) :
    inner ℂ (zeroExtend μ A hA f) g = inner ℂ f (restrictMap μ A g) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℂ (zeroExtend μ A hA f x) (g x) ∂μ) =
        ∫ x, A.indicator (fun y => inner ℂ (f y) (g y)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [zeroExtend_coe μ A hA f] with x hx
      rw [hx]
      by_cases hxA : x ∈ A <;> simp [hxA]
    _ = ∫ x in A, inner ℂ (f x) (g x) ∂μ := integral_indicator hA
    _ = ∫ x in A, inner ℂ (f x) (restrictMap μ A g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [restrict_coe μ A g] with x hx
      rw [hx]





end
end MeasureEquivalenceL2Restriction

end Source13

/- Preserved source skeleton: L2LocalizedOperators -/
section Source14
/-! Actual globalization and finite-measure localization of L2 module
operators, reducing a semifinite supported operator to the proved finite
measure multiplier theorem. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem restrict_indicator (A s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    restrictMap μ A (indicatorL2 μ hs f) =
      indicatorL2 (μ.restrict A) hs (restrictMap μ A f) := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (indicatorL2 μ hs f), restrict_coe μ A f,
    ae_restrict_of_ae (indicatorL2_coe μ hs f),
    indicatorL2_coe (μ.restrict A) hs (restrictMap μ A f)] with x hr hf hi ho
  rw [hr, hi, ho]
  by_cases hx : x ∈ s <;> simp [hx, hf]

theorem zeroExtend_indicator (A : Set X) (hA : MeasurableSet A)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)) :
    zeroExtend μ A hA (indicatorL2 (μ.restrict A) hs f) =
      indicatorL2 μ hs (zeroExtend μ A hA f) := by
  apply Lp.ext
  have hsrc := (ae_eq_restrict_iff_indicator_ae_eq hA).mp
    (indicatorL2_coe (μ.restrict A) hs f)
  filter_upwards [zeroExtend_coe μ A hA (indicatorL2 (μ.restrict A) hs f),
    zeroExtend_coe μ A hA f, indicatorL2_coe μ hs (zeroExtend μ A hA f), hsrc]
    with x he hf hi hsource
  rw [he, hi, hsource]
  by_cases hxA : x ∈ A <;> by_cases hxs : x ∈ s <;> simp [hxA, hxs, hf] at *















end
end MeasureEquivalenceL2Restriction

end Source14

/- Preserved source skeleton: L2ProjectionCommutantNormal -/
section Source15
/-! The finite-measure multiplication algebra is commutative and closed
under adjoints. In particular, a projection-commuting operator is normal.
This avoids introducing any abstract semifinite trace in the corner proof. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem inner_indicatorL2 (s : Set X) (hs : MeasurableSet s) (f g : Lp ℂ 2 μ) :
    inner ℂ (indicatorL2 μ hs f) g = inner ℂ f (indicatorL2 μ hs g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ hs f, indicatorL2_coe μ hs g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s <;> simp [hx]

theorem projectionCommutant_adjoint (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T.adjoint (indicatorL2 μ hs f) = indicatorL2 μ hs (T.adjoint f) := by
  intro s hs f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_indicatorL2,
    ← hT, ← ContinuousLinearMap.adjoint_inner_right, inner_indicatorL2]

variable [IsFiniteMeasure μ]

theorem projectionCommutant_commute
    (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hS : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      S (indicatorL2 μ hs f) = indicatorL2 μ hs (S f)) :
    T.comp S = S.comp T := by
  have hTm := projectionCommutant_eq_multiplier μ T hT
  have hSm := projectionCommutant_eq_multiplier μ S hS
  apply ContinuousLinearMap.ext
  intro f
  change T (S f) = S (T f)
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT) (S f),
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ S hS) f,
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ S hS) (T f),
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT) f]
      with x hTS hSf hST hTf
  rw [← hTm] at hTS hTf
  rw [← hSm] at hSf hST
  rw [hTS, hST, hSf, hTf]
  ring

theorem projectionCommutant_norm_adjoint
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) (f : Lp ℂ 2 μ) :
    ‖T f‖ = ‖T.adjoint f‖ := by
  have hcomm := projectionCommutant_commute μ T T.adjoint hT
    (projectionCommutant_adjoint μ T hT)
  have hnormal : IsStarNormal T := ⟨by
    change T.adjoint.comp T = T.comp T.adjoint
    exact hcomm.symm⟩
  exact (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp hnormal) f

end
end MeasureUnitary

end Source15

/- Preserved source skeleton: L2LocalizedAdjoints -/
section Source16
/-! Adjoint and reconstruction identities for actual finite compression.
They transfer normality of the finite multiplication algebra to the
norm comparison needed for individual semifinite matrix coefficients. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem globalize_adjoint (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) :
    (globalizeOperator μ A B hB T).adjoint = globalizeOperator μ B A hA T.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  change inner ℂ (zeroExtend μ A hA (T.adjoint (restrictMap μ B f))) g =
    inner ℂ f (zeroExtend μ B hB (T (restrictMap μ A g)))
  rw [inner_zeroExtend_restrict, ContinuousLinearMap.adjoint_inner_left]
  calc
    inner ℂ (restrictMap μ B f) (T (restrictMap μ A g)) =
        star (inner ℂ (T (restrictMap μ A g)) (restrictMap μ B f)) :=
      (inner_conj_symm _ _).symm
    _ = star (inner ℂ (zeroExtend μ B hB (T (restrictMap μ A g))) f) := by
      rw [inner_zeroExtend_restrict]
    _ = inner ℂ f (zeroExtend μ B hB (T (restrictMap μ A g))) := inner_conj_symm _ _









end
end MeasureEquivalenceL2Restriction

end Source16

/- Preserved source skeleton: L2SpectralProjectionIntertwining -/
section Source17
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

end Source17

/- Preserved source skeleton: KernelCantorNormalization -/
section Source18
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace SpectralDomination

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def normalizeNonzeroMeasure (μ : Measure Y) [IsFiniteMeasure μ] (hμ : μ ≠ 0) : ProbabilityMeasure Y :=
  ⟨(μ univ)⁻¹ • μ, ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (mt Measure.measure_univ_eq_zero.mp hμ) (measure_ne_top μ univ)⟩⟩

theorem normalizeNonzeroMeasure_equivalent (μ : Measure Y) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    μ ≪ (normalizeNonzeroMeasure μ hμ : Measure Y) ∧
      (normalizeNonzeroMeasure μ hμ : Measure Y) ≪ μ := by
  exact ⟨Measure.absolutelyContinuous_smul (by simp [measure_ne_top]), Measure.smul_absolutelyContinuous⟩

def normalizedKernelProbability (κ : Kernel X Y) [IsFiniteKernel κ] (hκ : ∀ x, κ x ≠ 0)
    (x : X) : ProbabilityMeasure Y := normalizeNonzeroMeasure (κ x) (hκ x)

theorem normalizedKernelProbability_measurable (κ : Kernel X Y) [IsFiniteKernel κ]
    (hκ : ∀ x, κ x ≠ 0) : Measurable (normalizedKernelProbability κ hκ) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable (fun x => (κ x univ)⁻¹ * κ x s)
  exact (Kernel.measurable_coe κ MeasurableSet.univ).inv.mul (Kernel.measurable_coe κ hs)

theorem map_ac_iff_of_measurableEmbedding (f : Y → Z) (hf : MeasurableEmbedding f) (μ ν : Measure Y) :
    μ.map f ≪ ν.map f ↔ μ ≪ ν := by
  constructor
  · intro h
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hzero
    have hz : ν.map f (f '' s) = 0 := by rw [hf.map_apply, hf.injective.preimage_image, hzero]
    have hm := h hz
    rwa [hf.map_apply, hf.injective.preimage_image] at hm
  · intro h
    exact h.map hf.measurable

def standardCantorEmbedding (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y] : Y → ℕ → Bool :=
  (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Y).choose

theorem standardCantorEmbedding_measurableEmbedding [StandardBorelSpace Y] :
    MeasurableEmbedding (standardCantorEmbedding Y) := by
  let h := (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Y).choose_spec
  exact h.1.measurableEmbedding h.2

def cantorKernelProbability [StandardBorelSpace Y] (κ : Kernel X Y) [IsFiniteKernel κ]
    (hκ : ∀ x, κ x ≠ 0) (x : X) : ProbabilityMeasure (ℕ → Bool) :=
  ⟨((normalizedKernelProbability κ hκ x : ProbabilityMeasure Y) : Measure Y).map (standardCantorEmbedding Y),
    Measure.isProbabilityMeasure_map (standardCantorEmbedding_measurableEmbedding.measurable.aemeasurable)⟩

theorem cantorKernelProbability_measurable [StandardBorelSpace Y]
    (κ : Kernel X Y) [IsFiniteKernel κ] (hκ : ∀ x, κ x ≠ 0) :
    Measurable (cantorKernelProbability κ hκ) := by
  apply Measurable.subtype_mk
  exact (Measure.measurable_map _ standardCantorEmbedding_measurableEmbedding.measurable).comp
    (measurable_subtype_coe.comp (normalizedKernelProbability_measurable κ hκ))

theorem cantorKernelProbability_classification [StandardBorelSpace Y]
    (κ : Kernel X Y) [IsFiniteKernel κ] (hκ : ∀ x, κ x ≠ 0) (x y : X) :
    ((cantorKernelProbability κ hκ x : Measure (ℕ → Bool)) ≪ cantorKernelProbability κ hκ y ∧
      (cantorKernelProbability κ hκ y : Measure (ℕ → Bool)) ≪ cantorKernelProbability κ hκ x) ↔
      (κ x ≪ κ y ∧ κ y ≪ κ x) := by
  change ((_ : Measure Y).map (standardCantorEmbedding Y) ≪ (_ : Measure Y).map (standardCantorEmbedding Y) ∧
    (_ : Measure Y).map (standardCantorEmbedding Y) ≪ (_ : Measure Y).map (standardCantorEmbedding Y)) ↔ _
  rw [map_ac_iff_of_measurableEmbedding _ standardCantorEmbedding_measurableEmbedding,
    map_ac_iff_of_measurableEmbedding _ standardCantorEmbedding_measurableEmbedding]
  have hx := normalizeNonzeroMeasure_equivalent (κ x) (hκ x)
  have hy := normalizeNonzeroMeasure_equivalent (κ y) (hκ y)
  constructor
  · rintro ⟨hab,hba⟩
    exact ⟨hx.1.trans (hab.trans hy.2),hy.1.trans (hba.trans hx.2)⟩
  · rintro ⟨hab,hba⟩
    exact ⟨hx.2.trans (hab.trans hy.1),hy.2.trans (hba.trans hx.1)⟩

end SpectralDomination

end
end Source18

/- Preserved source skeleton: WeightedDominatingKernel -/
section Source19
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

namespace SpectralDomination

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def weight (μ : ℕ → Measure Y) (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ (n + 1) * (1 + μ n univ)⁻¹

def weightedKernel (μ : X → ℕ → Measure Y)
    (hm : ∀ n, Measurable (fun x => μ x n)) (n : ℕ) : Kernel X Y where
  toFun x := weight (μ x) n • μ x n
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable (fun x => weight (μ x) n * μ x n s)
    apply Measurable.mul
    · exact measurable_const.mul
        (measurable_const.add ((Measure.measurable_coe MeasurableSet.univ).comp (hm n))).inv
    · exact (Measure.measurable_coe hs).comp (hm n)

theorem weightedKernel_mass_le (μ : X → ℕ → Measure Y) (hm) (n : ℕ) (x : X) :
    weightedKernel μ hm n x univ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
  change ((2⁻¹ : ℝ≥0∞) ^ (n + 1) * (1 + μ x n univ)⁻¹) * μ x n univ ≤ _
  rw [mul_assoc]
  calc
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ((1 + μ x n univ)⁻¹ * (1 + μ x n univ)) := by gcongr; exact le_add_self
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) * 1 := by gcongr; exact ENNReal.inv_mul_le_one _
    _ = _ := mul_one _

instance weightedKernel_finite (μ : X → ℕ → Measure Y)
    (hm : ∀ n, Measurable (fun x => μ x n)) (n : ℕ) :
    IsFiniteKernel (weightedKernel μ hm n) :=
  ⟨⟨(2⁻¹ : ℝ≥0∞) ^ (n + 1), by finiteness, weightedKernel_mass_le μ hm n⟩⟩

def dominatingKernel (μ : X → ℕ → Measure Y)
    (hm : ∀ n, Measurable (fun x => μ x n)) (base : Y) : Kernel X Y :=
  Kernel.const X (Measure.dirac base) + Kernel.sum (weightedKernel μ hm)

theorem dominatingKernel_mass_le (μ : X → ℕ → Measure Y) (hm) (base : Y) (x : X) :
    dominatingKernel μ hm base x univ ≤ 2 := by
  simp only [dominatingKernel, Kernel.add_apply, Kernel.const_apply, Measure.add_apply,
    Measure.dirac_apply_of_mem (mem_univ base), Kernel.sum_apply' _ _ MeasurableSet.univ]
  have hsum : (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1)) = 1 := by
    rw [ENNReal.tsum_geometric_add_one]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by finiteness)
  calc
    _ ≤ 1 + ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) := add_le_add le_rfl
      (ENNReal.tsum_le_tsum (fun n => weightedKernel_mass_le μ hm n x))
    _ = 2 := by rw [hsum]; norm_num

instance dominatingKernel_finite (μ : X → ℕ → Measure Y) (hm) (base : Y) :
    IsFiniteKernel (dominatingKernel μ hm base) :=
  ⟨⟨2, by norm_num, dominatingKernel_mass_le μ hm base⟩⟩

theorem weight_ne_zero (μ : ℕ → Measure Y) [∀ n, IsFiniteMeasure (μ n)] (n : ℕ) :
    weight μ n ≠ 0 := by
  simp only [weight, ne_eq, mul_eq_zero, pow_eq_zero_iff', ENNReal.inv_eq_zero,
    ENNReal.add_eq_top]
  simp [measure_ne_top]

theorem measure_ac_dominatingKernel (μ : X → ℕ → Measure Y) (hm) (base : Y)
    [∀ x n, IsFiniteMeasure (μ x n)] (x : X) (n : ℕ) :
    μ x n ≪ dominatingKernel μ hm base x := by
  have hscale : μ x n ≪ weightedKernel μ hm n x :=
    Measure.absolutelyContinuous_smul (weight_ne_zero (μ x) n)
  have hsum : weightedKernel μ hm n x ≪ Kernel.sum (weightedKernel μ hm) x := by
    rw [Kernel.sum_apply]
    exact Measure.absolutelyContinuous_sum_right n Measure.AbsolutelyContinuous.rfl
  exact (hscale.trans hsum).add_right' _

end SpectralDomination

end
end Source19

/- Preserved source skeleton: KernelSpectralSupports -/
section Source20
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

namespace SpectralDomination

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]

def kernelSupport (κ η : Kernel X Y) (x : X) : Set Y :=
  {y | κ.rnDeriv η x y ≠ 0}

theorem measurableSet_kernelSupport (κ η : Kernel X Y) (x : X) :
    MeasurableSet (kernelSupport κ η x) :=
  (Kernel.measurable_rnDeriv κ η).of_uncurry_left (measurableSet_singleton (0 : ℝ≥0∞)).compl

theorem measurableSet_kernelSupport_joint (κ η : Kernel X Y) :
    MeasurableSet {p : X × Y | p.2 ∈ kernelSupport κ η p.1} :=
  (Kernel.measurable_rnDeriv κ η) (measurableSet_singleton (0 : ℝ≥0∞)).compl

theorem kernel_support_equivalent (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (x : X) (hac : κ x ≪ η x) :
    κ x ≪ (η x).restrict (kernelSupport κ η x) ∧
      (η x).restrict (kernelSupport κ η x) ≪ κ x := by
  have he : (η x).withDensity (κ.rnDeriv η x) = κ x := by
    simpa only [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv κ η)] using
      (Kernel.withDensity_rnDeriv_eq (κ := κ) (η := η) hac)
  have hae : ae ((η x).withDensity (κ.rnDeriv η x)) =
      ae ((η x).restrict (kernelSupport κ η x)) := by
    apply Filter.ext
    intro s
    exact ae_withDensity_iff_ae_restrict (Kernel.measurable_rnDeriv κ η).of_uncurry_left
  rw [he] at hae
  exact ⟨Measure.ae_le_iff_absolutelyContinuous.mp hae.le,
    Measure.ae_le_iff_absolutelyContinuous.mp hae.ge⟩

def supportKernel (κ η : Kernel X Y) [IsFiniteKernel η] : Kernel X Y := by
  classical
  exact η.withDensity (fun x y => (kernelSupport κ η x).indicator (fun _ => 1) y)





instance supportKernel_finite (κ η : Kernel X Y) [IsFiniteKernel η] :
    IsFiniteKernel (supportKernel κ η) := by
  classical
  unfold supportKernel
  apply Kernel.isFiniteKernel_withDensity_of_bounded η (B := 1) (by simp)
  intro x y
  simp only [Set.indicator_apply]
  split_ifs <;> simp

end SpectralDomination

end
end Source20

/- Preserved source skeleton: UnitaryCyclicSubspace -/
section Source21
/-! The actual closed cyclic subspace of one unitary and its reducing
restriction. These are the first structural ingredients for the remaining
spectral-multiplicity classification, which is not asserted here. -/

open Set
open scoped InnerProductSpace

set_option maxHeartbeats 800000

namespace OperatorCoding

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cyclicSpan (U : StrongUnitary H) (v : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range (fun n : ℤ => (U ^ n) v))).topologicalClosure

theorem cyclicSpan_isClosed (U : StrongUnitary H) (v : H) :
    IsClosed (cyclicSpan U v : Set H) :=
  Submodule.isClosed_topologicalClosure _

theorem cyclicSpan_contains_orbit (U : StrongUnitary H) (v : H) (n : ℤ) :
    (U ^ n) v ∈ cyclicSpan U v :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self n))

theorem cyclicSpan_contains_generator (U : StrongUnitary H) (v : H) :
    v ∈ cyclicSpan U v := by
  simpa using cyclicSpan_contains_orbit U v 0

theorem cyclicSpan_minimal (U : StrongUnitary H) (v : H) (P : Submodule ℂ H)
    (hclosed : IsClosed (P : Set H)) (hcontains : ∀ n : ℤ, (U ^ n) v ∈ P) :
    cyclicSpan U v ≤ P :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro _ ⟨n,rfl⟩; exact hcontains n)) hclosed

theorem cyclicSpan_zpow_invariant (U : StrongUnitary H) (v : H) (m : ℤ)
    (x : H) (hx : x ∈ cyclicSpan U v) : (U ^ m) x ∈ cyclicSpan U v := by
  let P := Submodule.span ℂ (Set.range (fun n : ℤ => (U ^ n) v))
  have hspan : Set.MapsTo (U ^ m) (P : Set H) (P : Set H) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n,rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨m+n, ?_⟩
      change (U ^ (m+n)) v = (U ^ m) ((U ^ n) v)
      rw [zpow_add]
      rfl
    | zero => simpa only [map_zero] using P.zero_mem
    | add y z hy hz ihy ihz =>
      simpa only [map_add] using P.add_mem ihy ihz
    | smul a y hy ih =>
      simpa only [map_smul] using P.smul_mem a ih
  exact hspan.closure (U ^ m).continuous hx

def cyclicRestriction (U : StrongUnitary H) (v : H) :
    StrongUnitary (cyclicSpan U v) where
  toFun x := ⟨U x, by simpa only [zpow_one] using cyclicSpan_zpow_invariant U v 1 x x.property⟩
  invFun x := ⟨U.symm x, by
    simpa only [zpow_neg_one] using cyclicSpan_zpow_invariant U v (-1) x x.property⟩
  left_inv x := Subtype.ext (U.symm_apply_apply x)
  right_inv x := Subtype.ext (U.apply_symm_apply x)
  map_add' x y := Subtype.ext (U.map_add x y)
  map_smul' a x := Subtype.ext (U.map_smul a x)
  norm_map' x := U.norm_map x

theorem cyclicSpan_orthogonal_zpow_invariant (U : StrongUnitary H) (v : H) (m : ℤ)
    (x : H) (hx : x ∈ (cyclicSpan U v)ᗮ) : (U ^ m) x ∈ (cyclicSpan U v)ᗮ := by
  intro w hw
  have hw' : (U ^ m).symm w ∈ cyclicSpan U v := by
    simpa only [zpow_neg] using cyclicSpan_zpow_invariant U v (-m) w hw
  have hinner : inner ℂ w ((U ^ m) x) = inner ℂ ((U ^ m).symm w) x := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (U ^ m).inner_map_map ((U ^ m).symm w) x
  exact hinner.trans (hx _ hw')

end
end OperatorCoding

end Source21

/- Preserved source skeleton: UnitaryVectorRiesz -/
section Source22
/-! Actual finite vector-state Riesz measures for representations of a
commutative continuous-function algebra. This construction is used to
build cyclic spectral measures; no spectral classification is assumed. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace CompactlySupported

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def complexifyCompactSupport (f : C_c(K, ℝ)) : C(K, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

theorem complexifyCompactSupport_add (f g : C_c(K, ℝ)) :
    complexifyCompactSupport (f+g) = complexifyCompactSupport f + complexifyCompactSupport g := by
  ext x
  simp [complexifyCompactSupport]

theorem complexifyCompactSupport_smul (a : ℝ) (f : C_c(K, ℝ)) :
    complexifyCompactSupport (a • f) = (a : ℂ) • complexifyCompactSupport f := by
  ext x
  simp [complexifyCompactSupport, smul_eq_mul]

def representationVectorRealFunctional
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : C_c(K, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (inner ℂ v (π (complexifyCompactSupport f) v)).re
  map_add' f g := by
    rw [complexifyCompactSupport_add, map_add, ContinuousLinearMap.add_apply,
      inner_add_right, Complex.add_re]
  map_smul' a f := by
    rw [complexifyCompactSupport_smul, map_smul, ContinuousLinearMap.smul_apply,
      inner_smul_right]
    simp [Complex.mul_re, smul_eq_mul]

theorem representationVectorRealFunctional_nonneg
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (f : C_c(K, ℝ)) (hf : 0 ≤ f) :
    0 ≤ representationVectorRealFunctional π v f := by
  let g : C(K, ℂ) := ⟨fun x => (Real.sqrt (f x) : ℂ),
    Complex.continuous_ofReal.comp f.continuous.sqrt⟩
  have hfactor : complexifyCompactSupport f = star g * g := by
    ext x
    change (f x : ℂ) = star (Real.sqrt (f x) : ℂ) * (Real.sqrt (f x) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← pow_two, Real.sq_sqrt (hf x)]
  change 0 ≤ (inner ℂ v (π (complexifyCompactSupport f) v)).re
  rw [hfactor, map_mul, map_star]
  change 0 ≤ (inner ℂ v ((π g).adjoint ((π g) v))).re
  rw [ContinuousLinearMap.adjoint_inner_right]
  change 0 ≤ RCLike.re (inner ℂ ((π g) v) ((π g) v))
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact sq_nonneg ‖(π g) v‖

def representationVectorPositiveFunctional
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : C_c(K, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := representationVectorRealFunctional π v
  monotone' := by
    intro f g hfg
    have hnonneg := representationVectorRealFunctional_nonneg π v (g-f) (sub_nonneg.mpr hfg)
    simpa only [map_sub, sub_nonneg] using hnonneg

def representationVectorMeasure
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : Measure K :=
  RealRMK.rieszMeasure (representationVectorPositiveFunctional π v)

instance representationVectorMeasure_finite
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    IsFiniteMeasure (representationVectorMeasure π v) := by
  unfold representationVectorMeasure
  infer_instance

theorem representationVectorMeasure_integral
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C_c(K, ℝ)) :
    (∫ x, f x ∂representationVectorMeasure π v) =
      (inner ℂ v (π (complexifyCompactSupport f) v)).re :=
  RealRMK.integral_rieszMeasure (representationVectorPositiveFunctional π v) f

end
end MeasureUnitary

end Source22

/- Preserved source skeleton: UnitaryCircleFunctionalCalculus -/
section Source23
/-! The actual continuous-function representation on one fixed unit
circle supplied by the continuous functional calculus of a unitary. -/

open MeasureTheory Set Metric
open scoped ENNReal NNReal InnerProductSpace CStarAlgebra

set_option maxHeartbeats 1500000

namespace OperatorCoding

noncomputable section

abbrev SpectralCircle := Metric.sphere (0 : ℂ) 1

instance spectralCircle_compact : CompactSpace SpectralCircle :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ℂ) 1)

def circleCoordinate : C(SpectralCircle, ℂ) :=
  (ContinuousMap.id ℂ).restrict (Metric.sphere (0 : ℂ) 1)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

local instance _root_.OperatorCoding.instContinuousFunctionalCalculusComplexContinuousLinearMapIdIsStarNormal_unitaryCircleFunctionalCalculus : ContinuousFunctionalCalculus ℂ (H →L[ℂ] H) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

theorem strongUnitary_mem_unitary (U : StrongUnitary H) :
    (U : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H) :=
  (Unitary.linearIsometryEquiv.symm U).property

theorem strongUnitary_spectrum_circle (U : StrongUnitary H) :
    spectrum ℂ (U : H →L[ℂ] H) ⊆ Metric.sphere (0 : ℂ) 1 := by
  intro z hz
  simpa only [Metric.mem_sphere, dist_zero_right] using
    spectrum.norm_eq_one_of_unitary (strongUnitary_mem_unitary U) hz

def unitaryCircleRepresentation (U : StrongUnitary H) :
    C(SpectralCircle, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  cfcHomSuperset (R := ℂ) (a := (U : H →L[ℂ] H))
    (isStarNormal_of_mem_unitary (strongUnitary_mem_unitary U)) (strongUnitary_spectrum_circle U)

theorem unitaryCircleRepresentation_continuous (U : StrongUnitary H) :
    Continuous (unitaryCircleRepresentation U) :=
  cfcHomSuperset_continuous (isStarNormal_of_mem_unitary (strongUnitary_mem_unitary U))
    (strongUnitary_spectrum_circle U)

theorem unitaryCircleRepresentation_norm_le (U : StrongUnitary H) (f : C(SpectralCircle, ℂ)) :
    ‖unitaryCircleRepresentation U f‖ ≤ ‖f‖ := by
  unfold unitaryCircleRepresentation cfcHomSuperset
  rw [StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply,
    norm_cfcHom (U : H →L[ℂ] H) _ (isStarNormal_of_mem_unitary (strongUnitary_mem_unitary U))]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact ContinuousMap.norm_coe_le_norm f _

theorem unitaryCircleRepresentation_coordinate (U : StrongUnitary H) :
    unitaryCircleRepresentation U circleCoordinate = (U : H →L[ℂ] H) :=
  cfcHomSuperset_id (isStarNormal_of_mem_unitary (strongUnitary_mem_unitary U))
    (strongUnitary_spectrum_circle U)

theorem unitaryCircleRepresentation_coordinate_pow (U : StrongUnitary H) (n : ℕ) :
    unitaryCircleRepresentation U (circleCoordinate ^ n) = (U : H →L[ℂ] H) ^ n := by
  rw [map_pow, unitaryCircleRepresentation_coordinate]

theorem unitaryCircleRepresentation_star_coordinate (U : StrongUnitary H) :
    unitaryCircleRepresentation U (star circleCoordinate) = (U : H →L[ℂ] H).adjoint := by
  rw [map_star, unitaryCircleRepresentation_coordinate, ContinuousLinearMap.star_eq_adjoint]

def unitaryVectorSpectralMeasure (U : StrongUnitary H) (v : H) : Measure SpectralCircle :=
  MeasureUnitary.representationVectorMeasure (unitaryCircleRepresentation U) v

instance unitaryVectorSpectralMeasure_finite (U : StrongUnitary H) (v : H) :
    IsFiniteMeasure (unitaryVectorSpectralMeasure U v) := by
  unfold unitaryVectorSpectralMeasure
  infer_instance

end
end OperatorCoding

end Source23

/- Preserved source skeleton: UnitaryCFCStrongContinuity -/
section Source24
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace CStarAlgebra

set_option maxHeartbeats 1500000

noncomputable section

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

def stronglyContinuousFunctions : Set C(SpectralCircle, ℂ) :=
  {f | ∀ x : H, Continuous (fun U : StrongUnitary H => unitaryCircleRepresentation U f x)}

theorem stronglyContinuousFunctions_closed :
    IsClosed (stronglyContinuousFunctions (H := H)) := by
  apply isClosed_of_closure_subset
  intro f hf x
  apply continuous_of_uniform_approx_of_continuous
  intro V hV
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_uniformity_dist.mp hV
  have hxpos : 0 < ‖x‖ + 1 := by positivity
  obtain ⟨g,hg,hgf⟩ := Metric.mem_closure_iff.mp hf (ε / (‖x‖+1)) (by positivity)
  have hfg : ‖f-g‖ < ε / (‖x‖+1) := by simpa only [dist_eq_norm, norm_sub_rev] using hgf
  refine ⟨fun U : StrongUnitary H => unitaryCircleRepresentation U g x, hg x, ?_⟩
  intro U
  apply hεV
  change dist (unitaryCircleRepresentation U f x) (unitaryCircleRepresentation U g x) < ε
  calc
    dist (unitaryCircleRepresentation U f x) (unitaryCircleRepresentation U g x) =
        ‖unitaryCircleRepresentation U (f-g) x‖ := by
          rw [dist_eq_norm,map_sub,ContinuousLinearMap.sub_apply]
    _ ≤ ‖unitaryCircleRepresentation U (f-g)‖ * ‖x‖ :=
      (unitaryCircleRepresentation U (f-g)).le_opNorm x
    _ ≤ ‖f-g‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right (unitaryCircleRepresentation_norm_le U (f-g)) (norm_nonneg x)
    _ ≤ ‖f-g‖ * (‖x‖+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ < (ε/(‖x‖+1)) * (‖x‖+1) := mul_lt_mul_of_pos_right hfg hxpos
    _ = ε := div_mul_cancel₀ _ (ne_of_gt hxpos)

def stronglyContinuousStarAlgebra : StarSubalgebra ℂ C(SpectralCircle, ℂ) where
  carrier := {f | f ∈ stronglyContinuousFunctions (H := H) ∧
    star f ∈ stronglyContinuousFunctions (H := H)}
  zero_mem' := by
    constructor <;> intro x <;>
      simpa only [map_zero,ContinuousLinearMap.zero_apply,star_zero] using
        (continuous_const (y := (0 : H)) : Continuous (fun _ : StrongUnitary H => (0 : H)))
  one_mem' := by
    constructor <;> intro x <;>
      simpa only [map_one,ContinuousLinearMap.one_apply,star_one] using
        (continuous_const (y := x) : Continuous (fun _ : StrongUnitary H => x))
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x
      simpa only [map_add,ContinuousLinearMap.add_apply] using (hf.1 x).add (hg.1 x)
    · intro x
      simpa only [star_add,map_add,ContinuousLinearMap.add_apply] using (hf.2 x).add (hg.2 x)
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro x
      simpa only [map_mul,ContinuousLinearMap.mul_apply] using
        strongOperator_continuous_action (A := fun U : StrongUnitary H => unitaryCircleRepresentation U f)
          hf.1 (fun U => unitaryCircleRepresentation_norm_le U f) (hg.1 x)
    · intro x
      simpa only [star_mul,map_mul,ContinuousLinearMap.mul_apply] using
        strongOperator_continuous_action (A := fun U : StrongUnitary H => unitaryCircleRepresentation U (star g))
          hg.2 (fun U => unitaryCircleRepresentation_norm_le U (star g)) (hf.2 x)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x
      simpa only [Algebra.algebraMap_eq_smul_one,map_smul,map_one,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply] using
        (continuous_const (y := c • x) : Continuous (fun _ : StrongUnitary H => c • x))
    · intro x
      simpa only [Algebra.algebraMap_eq_smul_one,star_smul,star_one,map_smul,map_one,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply] using
        (continuous_const (y := star c • x) : Continuous (fun _ : StrongUnitary H => star c • x))
  star_mem' := by intro f hf; exact ⟨hf.2,by simpa only [star_star] using hf.1⟩

theorem stronglyContinuousStarAlgebra_closed :
    IsClosed (stronglyContinuousStarAlgebra (H := H) : Set C(SpectralCircle, ℂ)) :=
  stronglyContinuousFunctions_closed.inter (stronglyContinuousFunctions_closed.preimage continuous_star)

theorem circleCoordinate_mem_stronglyContinuousStarAlgebra :
    circleCoordinate ∈ stronglyContinuousStarAlgebra (H := H) := by
  constructor
  · intro x
    simpa only [unitaryCircleRepresentation_coordinate] using strongUnitary_continuous_eval x
  · intro x
    have hc : Continuous (fun U : StrongUnitary H => U⁻¹ x) :=
      (strongUnitary_continuous_eval x).comp continuous_inv
    simpa only [unitaryCircleRepresentation_star_coordinate,LinearIsometryEquiv.adjoint_eq_symm] using hc

theorem unitaryCircleRepresentation_strong_continuous (f : C(SpectralCircle, ℂ)) (x : H) :
    Continuous (fun U : StrongUnitary H => unitaryCircleRepresentation U f x) := by
  let A := stronglyContinuousStarAlgebra (H := H)
  have hsep : A.SeparatesPoints := by
    intro z w hzw
    refine ⟨circleCoordinate,⟨circleCoordinate,circleCoordinate_mem_stronglyContinuousStarAlgebra,rfl⟩,?_⟩
    intro he
    exact hzw (Subtype.ext he)
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hf : f ∈ closure (A : Set C(SpectralCircle, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe,htop]
    trivial
  exact ((stronglyContinuousStarAlgebra_closed (H := H)).closure_subset hf).1 x

theorem unitaryCircleRepresentation_joint_continuous (f : C(SpectralCircle, ℂ)) :
    Continuous (fun p : StrongUnitary H × H => unitaryCircleRepresentation p.1 f p.2) :=
  strongOperator_continuous_action
    (fun x => (unitaryCircleRepresentation_strong_continuous f x).comp continuous_fst)
    (fun p => unitaryCircleRepresentation_norm_le p.1 f) continuous_snd

end OperatorCoding

end
end Source24

/- Preserved source skeleton: UnitaryVectorRieszMass -/
section Source25
open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace CompactlySupported

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureUnitary

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def realContinuousCompactSupport (f : C(K, ℝ)) : C_c(K, ℝ) :=
  ⟨f, HasCompactSupport.of_compactSpace f⟩

theorem representationVectorMeasure_mass_toReal
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    (representationVectorMeasure π v Set.univ).toReal = ‖v‖ ^ 2 := by
  let oneC : C_c(K, ℝ) := realContinuousCompactSupport 1
  have hone : complexifyCompactSupport oneC = 1 := by
    ext x
    simp [complexifyCompactSupport, oneC, realContinuousCompactSupport]
  have h := representationVectorMeasure_integral π v oneC
  rw [hone, map_one] at h
  simpa [oneC, realContinuousCompactSupport, Measure.real,
    inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h



def continuousNormSquare (f : C(K, ℂ)) : C(K, ℝ) :=
  ⟨fun x => ‖f x‖ ^ 2, f.continuous.norm.pow 2⟩

theorem complexify_normSquare (f : C(K, ℂ)) :
    complexifyCompactSupport (realContinuousCompactSupport (continuousNormSquare f)) =
      star f * f := by
  ext x
  change ((‖f x‖ ^ 2 : ℝ) : ℂ) = star (f x) * f x
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.normSq_eq_conj_mul_self (z := f x)

theorem representationVectorMeasure_integral_norm_sq
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(K, ℂ)) :
    (∫ x, ‖f x‖ ^ 2 ∂representationVectorMeasure π v) = ‖π f v‖ ^ 2 := by
  have h := representationVectorMeasure_integral π v
    (realContinuousCompactSupport (continuousNormSquare f))
  rw [complexify_normSquare, map_mul, map_star] at h
  change (∫ x, ‖f x‖ ^ 2 ∂representationVectorMeasure π v) =
    (inner ℂ v ((π f).adjoint (π f v))).re at h
  rw [ContinuousLinearMap.adjoint_inner_right] at h
  change (∫ x, ‖f x‖ ^ 2 ∂representationVectorMeasure π v) =
    RCLike.re (inner ℂ (π f v) (π f v)) at h
  rw [← norm_sq_eq_re_inner] at h
  exact h

end MeasureUnitary

end
end Source25

/- Preserved source skeleton: UnitaryCyclicRiesz -/
section Source26
open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace

set_option maxHeartbeats 1200000

noncomputable section

namespace MeasureUnitary

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def representationVectorLinearMap (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    C(K, ℂ) →ₗ[ℂ] H where
  toFun f := π f v
  map_add' f g := by simp
  map_smul' c f := by simp

theorem representationVector_norm_toLp
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(K, ℂ)) :
    ‖π f v‖ = ‖ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f‖ := by
  have h := representationVectorMeasure_integral_norm_sq π v f
  have he : (∫ x, ‖f x‖ ^ 2 ∂representationVectorMeasure π v) =
      ‖ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f‖ ^ 2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) (representationVectorMeasure π v)] with x hx
    rw [hx]
  nlinarith [norm_nonneg (π f v),
    norm_nonneg (ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f)]

instance representationVectorMeasure_weaklyRegular
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    (representationVectorMeasure π v).WeaklyRegular := by
  unfold representationVectorMeasure
  infer_instance

def representationVectorLpOperator
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    Lp ℂ 2 (representationVectorMeasure π v) →L[ℂ] H :=
  (representationVectorLinearMap π v).extendOfNorm
    (ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ).toLinearMap

theorem representationVectorLpOperator_toLp
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(K, ℂ)) :
    representationVectorLpOperator π v
      (ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f) = π f v := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange (p := 2) ℂ (representationVectorMeasure π v) ℂ (by norm_num)
  · refine ⟨1, fun g => ?_⟩
    simpa only [one_mul] using (representationVector_norm_toLp π v g).le

theorem representationVectorLpOperator_norm
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (f : Lp ℂ 2 (representationVectorMeasure π v)) :
    ‖representationVectorLpOperator π v f‖ = ‖f‖ := by
  have hd := ContinuousMap.toLp_denseRange (p := 2) ℂ (representationVectorMeasure π v) ℂ (by norm_num)
  refine hd.induction ?_ ?_ f
  · rintro z ⟨g, rfl⟩
    rw [representationVectorLpOperator_toLp]
    exact representationVector_norm_toLp π v g
  · exact isClosed_eq (continuous_norm.comp (representationVectorLpOperator π v).continuous) continuous_norm

def representationVectorLpIsometry
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    Lp ℂ 2 (representationVectorMeasure π v) →ₗᵢ[ℂ] H where
  __ := (representationVectorLpOperator π v).toLinearMap
  norm_map' := representationVectorLpOperator_norm π v

end MeasureUnitary

end
end Source26

/- Preserved source skeleton: UnitaryCyclicRieszRange -/
section Source27
open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureUnitary

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def representationCyclicSubspace
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : Submodule ℂ H :=
  (representationVectorLinearMap π v).range.topologicalClosure

theorem representationVectorLpIsometry_toLp
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (f : C(K, ℂ)) :
    representationVectorLpIsometry π v
      (ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ f) = π f v :=
  representationVectorLpOperator_toLp π v f

theorem representationVectorLpIsometry_mem
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (f : Lp ℂ 2 (representationVectorMeasure π v)) :
    representationVectorLpIsometry π v f ∈ representationCyclicSubspace π v := by
  have hd := ContinuousMap.toLp_denseRange (p := 2) ℂ (representationVectorMeasure π v) ℂ (by norm_num)
  refine hd.induction ?_ ?_ f
  · rintro z ⟨g,rfl⟩
    rw [representationVectorLpIsometry_toLp]
    exact (representationVectorLinearMap π v).range.le_topologicalClosure ⟨g,rfl⟩
  · exact (representationVectorLinearMap π v).range.isClosed_topologicalClosure.preimage
      (representationVectorLpIsometry π v).continuous

theorem representationCyclicSubspace_le_range
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    representationCyclicSubspace π v ≤ (representationVectorLpIsometry π v).toLinearMap.range := by
  apply Submodule.topologicalClosure_minimal
  · rintro z ⟨g,rfl⟩
    refine ⟨ContinuousMap.toLp 2 (representationVectorMeasure π v) ℂ g, ?_⟩
    exact representationVectorLpIsometry_toLp π v g
  · exact (representationVectorLpIsometry π v).isometry.isClosedEmbedding.isClosed_range

def representationCyclicLpIsometry
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    Lp ℂ 2 (representationVectorMeasure π v) →ₗᵢ[ℂ] representationCyclicSubspace π v where
  toLinearMap := (representationVectorLpIsometry π v).toLinearMap.codRestrict
    (representationCyclicSubspace π v) (representationVectorLpIsometry_mem π v)
  norm_map' := (representationVectorLpIsometry π v).norm_map

def representationCyclicLpEquiv
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    Lp ℂ 2 (representationVectorMeasure π v) ≃ₗᵢ[ℂ] representationCyclicSubspace π v :=
  LinearIsometryEquiv.ofSurjective (representationCyclicLpIsometry π v) (by
    intro z
    obtain ⟨f,hf⟩ := representationCyclicSubspace_le_range π v z.property
    refine ⟨f,Subtype.ext hf⟩)

end MeasureUnitary

end
end Source27

/- Preserved source skeleton: UnitaryCyclicRieszIntertwining -/
section Source28
open MeasureTheory Filter Set
open scoped ENNReal NNReal InnerProductSpace

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureUnitary

variable {K H : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuousMultiplierL2_toLp (μ : Measure K) [IsFiniteMeasure μ]
    (a f : C(K, ℂ)) :
    continuousMultiplierL2 μ a (ContinuousMap.toLp 2 μ ℂ f) =
      ContinuousMap.toLp 2 μ ℂ (a * f) := by
  apply Lp.ext
  filter_upwards [continuousMultiplierL2_coe μ a (ContinuousMap.toLp 2 μ ℂ f),
    f.coeFn_toLp (p := 2) (𝕜 := ℂ) μ,
    (a*f).coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with x hmul hf haf
  rw [hmul, hf, haf]
  rfl

theorem representationVectorLpOperator_intertwines
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (a : C(K, ℂ))
    (f : Lp ℂ 2 (representationVectorMeasure π v)) :
    representationVectorLpOperator π v
      (continuousMultiplierL2 (representationVectorMeasure π v) a f) =
      π a (representationVectorLpOperator π v f) := by
  have hd := ContinuousMap.toLp_denseRange (p := 2) ℂ (representationVectorMeasure π v) ℂ (by norm_num)
  refine hd.induction ?_ ?_ f
  · rintro z ⟨g,rfl⟩
    rw [continuousMultiplierL2_toLp, representationVectorLpOperator_toLp,
      representationVectorLpOperator_toLp, map_mul]
    rfl
  · exact isClosed_eq
      ((representationVectorLpOperator π v).continuous.comp
        (continuousMultiplierL2 (representationVectorMeasure π v) a).continuous)
      ((π a).continuous.comp (representationVectorLpOperator π v).continuous)

theorem representationVectorLpIsometry_intertwines
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (a : C(K, ℂ))
    (f : Lp ℂ 2 (representationVectorMeasure π v)) :
    representationVectorLpIsometry π v
      (continuousMultiplierL2 (representationVectorMeasure π v) a f) =
      π a (representationVectorLpIsometry π v f) :=
  representationVectorLpOperator_intertwines π v a f

end MeasureUnitary

end
end Source28

/- Preserved source skeleton: FiniteOrthogonalProjection -/
section Source29
/-! A finite orthogonal family, allowing zero entries, gives its actual
orthogonal projection by the usual measurable coefficient formula. -/

open MeasureTheory Set Finset Filter Topology
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteFamilySpan (f : ℕ → H) (n : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (f '' Set.Iio n)

instance finiteFamilySpan_finiteDimensional (f : ℕ → H) (n : ℕ) :
    FiniteDimensional ℂ (finiteFamilySpan f n) :=
  FiniteDimensional.span_of_finite ℂ ((Set.finite_Iio n).image f)

def finiteOrthogonalProjection (f : ℕ → H) (n : ℕ) (x : H) : H :=
  ∑ i ∈ Finset.range n, (inner ℂ (f i) x / inner ℂ (f i) (f i)) • f i

theorem finiteOrthogonalProjection_mem (f : ℕ → H) (n : ℕ) (x : H) :
    finiteOrthogonalProjection f n x ∈ finiteFamilySpan f n := by
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, Finset.mem_range.mp hi, rfl⟩

theorem finiteOrthogonalProjection_inner (f : ℕ → H)
    (horth : Pairwise (fun i j => inner ℂ (f i) (f j) = 0))
    (n : ℕ) (x : H) (i : ℕ) (hi : i < n) :
    inner ℂ (f i) (x - finiteOrthogonalProjection f n x) = 0 := by
  rw [inner_sub_right]
  have hsum : inner ℂ (f i) (finiteOrthogonalProjection f n x) = inner ℂ (f i) x := by
    rw [finiteOrthogonalProjection, inner_sum]
    rw [Finset.sum_eq_single i]
    · rw [inner_smul_right]
      by_cases hzero : f i = 0
      · simp [hzero]
      · exact div_mul_cancel₀ _ (inner_self_ne_zero.mpr hzero)
    · intro j hj hji
      rw [inner_smul_right, horth hji.symm, mul_zero]
    · intro hni
      exact (hni (Finset.mem_range.mpr hi)).elim
  rw [hsum, sub_self]

theorem finiteOrthogonalProjection_eq_starProjection (f : ℕ → H)
    (horth : Pairwise (fun i j => inner ℂ (f i) (f j) = 0)) (n : ℕ) (x : H) :
    finiteOrthogonalProjection f n x = (finiteFamilySpan f n).starProjection x := by
  symm
  apply (finiteFamilySpan f n).eq_starProjection_of_mem_of_inner_eq_zero
    (finiteOrthogonalProjection_mem f n x)
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    rw [inner_eq_zero_symm]
    exact finiteOrthogonalProjection_inner f horth n x i hi
  | zero => simp
  | add u v hu hv ihu ihv => simp only [inner_add_right, ihu, ihv, add_zero]
  | smul a u hu ihu => simp only [inner_smul_right, ihu, mul_zero]

variable {S : Type*} [MeasurableSpace S] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]

theorem finiteOrthogonalProjection_measurable (f : S → ℕ → H)
    (hf : ∀ i, Measurable (fun s => f s i)) (x : S → H) (hx : Measurable x) (n : ℕ) :
    Measurable (fun s => finiteOrthogonalProjection (f s) n (x s)) := by
  unfold finiteOrthogonalProjection
  apply Finset.measurable_sum
  intro i hi
  exact ((hf i).inner hx |>.div ((hf i).inner (hf i))).smul (hf i)

end
end MeasureUnitary

end Source29

/- Preserved source skeleton: CountableSpanProjectionBorel -/
section Source30
/-! Projection onto the closed span of a Borel countable family is
Borel. Finite Gram--Schmidt coefficient sums supply the actual limits. -/

open MeasureTheory Set Finset Filter Topology InnerProductSpace
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def closedFamilySpan (f : ℕ → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range f)).topologicalClosure

instance closedFamilySpan_complete (f : ℕ → H) : CompleteSpace (closedFamilySpan f) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

theorem starProjection_eq_of_submodule_eq (P Q : Submodule ℂ H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] (hPQ : P = Q) :
    P.starProjection = Q.starProjection := by
  subst Q
  rfl

theorem finiteFamilySpan_mono (f : ℕ → H) : Monotone (finiteFamilySpan f) := by
  intro n m hnm
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi hnm, rfl⟩

theorem iSup_finiteFamilySpan (f : ℕ → H) :
    (⨆ n : ℕ, finiteFamilySpan f n) = Submodule.span ℂ (Set.range f) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply (le_iSup (finiteFamilySpan f) (i+1))
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self i, rfl⟩

theorem finiteOrthogonalProjection_tendsto (f : ℕ → H)
    (horth : Pairwise (fun i j => inner ℂ (f i) (f j) = 0)) (x : H) :
    Tendsto (fun n => finiteOrthogonalProjection f n x) atTop
      (𝓝 ((closedFamilySpan f).starProjection x)) := by
  letI : ((⨆ n, finiteFamilySpan f n).topologicalClosure).HasOrthogonalProjection := by
    rw [iSup_finiteFamilySpan]
    change (closedFamilySpan f).HasOrthogonalProjection
    infer_instance
  have h := Submodule.starProjection_tendsto_closure_iSup (finiteFamilySpan f)
    (finiteFamilySpan_mono f) x
  have heq := starProjection_eq_of_submodule_eq
    (⨆ n, finiteFamilySpan f n).topologicalClosure (closedFamilySpan f)
      (congrArg Submodule.topologicalClosure (iSup_finiteFamilySpan f))
  simpa only [heq, finiteOrthogonalProjection_eq_starProjection f horth] using h

variable {S : Type*} [MeasurableSpace S] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H]

theorem closedFamilySpan_projection_measurable (f : S → ℕ → H)
    (hf : ∀ i, Measurable (fun s => f s i)) (x : S → H) (hx : Measurable x) :
    Measurable (fun s => (closedFamilySpan (f s)).starProjection (x s)) := by
  let g : S → ℕ → H := fun s => gramSchmidt ℂ (f s)
  have hg : ∀ i, Measurable (fun s => g s i) := measurable_gramSchmidt f hf
  have hspan (s : S) : closedFamilySpan (g s) = closedFamilySpan (f s) := by
    unfold closedFamilySpan g
    rw [span_gramSchmidt]
  have hlim : Tendsto (fun n s => finiteOrthogonalProjection (g s) n (x s)) atTop
      (𝓝 (fun s => (closedFamilySpan (f s)).starProjection (x s))) := by
    apply tendsto_pi_nhds.mpr
    intro s
    have heq := starProjection_eq_of_submodule_eq (closedFamilySpan (g s))
      (closedFamilySpan (f s)) (hspan s)
    simpa only [heq] using
      finiteOrthogonalProjection_tendsto (g s) (gramSchmidt_pairwise_orthogonal ℂ (f s)) (x s)
  exact measurable_of_tendsto_metrizable (fun n => finiteOrthogonalProjection_measurable g hg x hx n) hlim

end
end MeasureUnitary

end Source30

/- Preserved source skeleton: UnitaryCyclicProjectionBorel -/
section Source31
/-! Borel orthogonal projections onto the actual cyclic subspaces of
unitaries, with both the generator vector and test vector varying. -/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

set_option maxHeartbeats 1000000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

def integerEnumeration : ℕ → ℤ := Classical.choose (exists_surjective_nat ℤ)

theorem integerEnumeration_surjective : Function.Surjective integerEnumeration :=
  Classical.choose_spec (exists_surjective_nat ℤ)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance cyclicSpan_complete (U : StrongUnitary H) (v : H) : CompleteSpace (cyclicSpan U v) :=
  (cyclicSpan_isClosed U v).isComplete.completeSpace_coe





variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

local instance _root_.OperatorCoding.instMeasurableSpaceStrongUnitary_unitaryCyclicProjectionBorel : MeasurableSpace (StrongUnitary H) := borel _
local instance _root_.OperatorCoding.instBorelSpaceStrongUnitary_unitaryCyclicProjectionBorel : BorelSpace (StrongUnitary H) := ⟨rfl⟩



end
end OperatorCoding

end Source31

/- Preserved source skeleton: UnitaryCyclicFunctionalCalculus -/
section Source32
/-! The continuous functional calculus preserves the actual closed
Laurent-orbit cyclic subspace. The proof uses a closed star subalgebra
and Stone--Weierstrass, with no spectral theorem assumed. -/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace CStarAlgebra

set_option maxHeartbeats 2000000

namespace OperatorCoding

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

def cyclicPreservingFunctions (U : StrongUnitary H) (v : H) :
    StarSubalgebra ℂ C(SpectralCircle, ℂ) where
  carrier := {f | (∀ x ∈ cyclicSpan U v, unitaryCircleRepresentation U f x ∈ cyclicSpan U v) ∧
    (∀ x ∈ cyclicSpan U v, unitaryCircleRepresentation U (star f) x ∈ cyclicSpan U v)}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x hx
      simpa only [map_add, ContinuousLinearMap.add_apply] using
        (cyclicSpan U v).add_mem (hf.1 x hx) (hg.1 x hx)
    · intro x hx
      simpa only [star_add, map_add, ContinuousLinearMap.add_apply] using
        (cyclicSpan U v).add_mem (hf.2 x hx) (hg.2 x hx)
  mul_mem' := by
    intro f g hf hg
    constructor
    · intro x hx
      simpa only [map_mul, ContinuousLinearMap.mul_apply] using hf.1 _ (hg.1 x hx)
    · intro x hx
      simpa only [star_mul, map_mul, ContinuousLinearMap.mul_apply] using hg.2 _ (hf.2 x hx)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x hx
      simpa only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using
        (cyclicSpan U v).smul_mem c hx
    · intro x hx
      simpa only [Algebra.algebraMap_eq_smul_one, star_smul, star_one, map_smul, map_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] using
        (cyclicSpan U v).smul_mem (star c) hx
  star_mem' := by
    intro f hf
    exact ⟨hf.2, by simpa only [star_star] using hf.1⟩

theorem cyclicPreservingFunctions_closed (U : StrongUnitary H) (v : H) :
    IsClosed (cyclicPreservingFunctions U v : Set C(SpectralCircle, ℂ)) := by
  have heval (x : H) : Continuous (fun f : C(SpectralCircle, ℂ) => unitaryCircleRepresentation U f x) :=
    (ContinuousLinearMap.apply ℂ H x).continuous.comp (unitaryCircleRepresentation_continuous U)
  have hc := cyclicSpan_isClosed U v
  have hfirst : IsClosed {f : C(SpectralCircle, ℂ) |
      ∀ x ∈ cyclicSpan U v, unitaryCircleRepresentation U f x ∈ cyclicSpan U v} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun x : H => isClosed_iInter (fun _hx : x ∈ cyclicSpan U v => hc.preimage (heval x)))
  have hsecond : IsClosed {f : C(SpectralCircle, ℂ) |
      ∀ x ∈ cyclicSpan U v, unitaryCircleRepresentation U (star f) x ∈ cyclicSpan U v} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun x : H => isClosed_iInter (fun _hx : x ∈ cyclicSpan U v =>
        hc.preimage ((heval x).comp continuous_star)))
  exact hfirst.inter hsecond

theorem circleCoordinate_mem_cyclicPreservingFunctions (U : StrongUnitary H) (v : H) :
    circleCoordinate ∈ cyclicPreservingFunctions U v := by
  constructor
  · intro x hx
    rw [unitaryCircleRepresentation_coordinate]
    simpa only [zpow_one] using cyclicSpan_zpow_invariant U v 1 x hx
  · intro x hx
    rw [unitaryCircleRepresentation_star_coordinate, U.adjoint_eq_symm]
    simpa only [zpow_neg_one] using cyclicSpan_zpow_invariant U v (-1) x hx

theorem unitaryCircleRepresentation_cyclicSpan_invariant (U : StrongUnitary H) (v : H)
    (f : C(SpectralCircle, ℂ)) (x : H) (hx : x ∈ cyclicSpan U v) :
    unitaryCircleRepresentation U f x ∈ cyclicSpan U v := by
  let A := cyclicPreservingFunctions U v
  have hsep : A.SeparatesPoints := by
    intro z w hzw
    refine ⟨circleCoordinate, ⟨circleCoordinate,
      circleCoordinate_mem_cyclicPreservingFunctions U v, rfl⟩, ?_⟩
    intro he
    exact hzw (Subtype.ext he)
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hf : f ∈ closure (A : Set C(SpectralCircle, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]
    trivial
  exact ((cyclicPreservingFunctions_closed U v).closure_subset hf).1 x hx

end
end OperatorCoding

end Source32

/- Preserved source skeleton: UnitaryCyclicSpectralSubspace -/
section Source33
/-! The Riesz cyclic representation space is exactly the actual closed
Laurent-orbit cyclic subspace of the original unitary. -/

open MeasureTheory Set
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

theorem strongUnitary_clm_pow_apply (U : StrongUnitary H) (n : ℕ) (x : H) :
    ((U : H →L[ℂ] H) ^ n) x = (U ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, pow_succ']
    exact congrArg U ih

theorem representationCyclicSubspace_unitaryCircle_eq (U : StrongUnitary H) (v : H) :
    representationCyclicSubspace (unitaryCircleRepresentation U) v = cyclicSpan U v := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (cyclicSpan_isClosed U v)
    rintro x ⟨f,rfl⟩
    exact unitaryCircleRepresentation_cyclicSpan_invariant U v f v (cyclicSpan_contains_generator U v)
  · apply cyclicSpan_minimal U v _
      ((representationVectorLinearMap (unitaryCircleRepresentation U) v).range.isClosed_topologicalClosure)
    intro n
    cases n with
    | ofNat m =>
      have hmem : unitaryCircleRepresentation U (circleCoordinate ^ m) v ∈
          representationCyclicSubspace (unitaryCircleRepresentation U) v :=
        Submodule.le_topologicalClosure _ ⟨circleCoordinate ^ m,rfl⟩
      simpa only [unitaryCircleRepresentation_coordinate_pow, strongUnitary_clm_pow_apply,
        zpow_natCast] using hmem
    | negSucc m =>
      have hmem : unitaryCircleRepresentation U ((star circleCoordinate) ^ (m+1)) v ∈
          representationCyclicSubspace (unitaryCircleRepresentation U) v :=
        Submodule.le_topologicalClosure _ ⟨(star circleCoordinate) ^ (m+1),rfl⟩
      rw [map_pow, unitaryCircleRepresentation_star_coordinate, U.adjoint_eq_symm,
        strongUnitary_clm_pow_apply] at hmem
      change ((U⁻¹) ^ (m+1)) v ∈ representationCyclicSubspace (unitaryCircleRepresentation U) v at hmem
      simpa only [zpow_negSucc, inv_pow] using hmem

end
end OperatorCoding

end Source33

/- Preserved source skeleton: UnitaryCyclicSpectralModel -/
section Source34
/-! The cyclic spectral theorem for an actual unitary: its closed cyclic
subspace is unitarily equivalent to coordinate multiplication on the
actual finite Riesz vector measure on the fixed circle. -/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def submoduleIsometryOfEq (P Q : Submodule ℂ H) (hPQ : P = Q) : P ≃ₗᵢ[ℂ] Q := by
  subst Q
  exact LinearIsometryEquiv.refl ℂ P

theorem submoduleIsometryOfEq_coe (P Q : Submodule ℂ H) (hPQ : P = Q) (x : P) :
    ((submoduleIsometryOfEq P Q hPQ x : Q) : H) = x := by
  subst Q
  rfl

end
end MeasureUnitary

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

theorem circleCoordinate_norm (z : SpectralCircle) : ‖circleCoordinate z‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using z.property

def spectralCoordinateUnitary (μ : Measure SpectralCircle) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  phaseEquiv μ circleCoordinate circleCoordinate.continuous.measurable circleCoordinate_norm

def unitaryCyclicLpEquiv (U : StrongUnitary H) (v : H) :
    Lp ℂ 2 (unitaryVectorSpectralMeasure U v) ≃ₗᵢ[ℂ] cyclicSpan U v :=
  (representationCyclicLpEquiv (unitaryCircleRepresentation U) v).trans
    (submoduleIsometryOfEq _ _ (representationCyclicSubspace_unitaryCircle_eq U v))

theorem unitaryCyclicLpEquiv_coe (U : StrongUnitary H) (v : H)
    (f : Lp ℂ 2 (unitaryVectorSpectralMeasure U v)) :
    ((unitaryCyclicLpEquiv U v f : cyclicSpan U v) : H) =
      representationVectorLpIsometry (unitaryCircleRepresentation U) v f := by
  change ((submoduleIsometryOfEq _ _ (representationCyclicSubspace_unitaryCircle_eq U v)
    (representationCyclicLpEquiv (unitaryCircleRepresentation U) v f) : cyclicSpan U v) : H) = _
  rw [submoduleIsometryOfEq_coe]
  rfl

theorem unitaryCyclicLpEquiv_intertwines (U : StrongUnitary H) (v : H)
    (f : Lp ℂ 2 (unitaryVectorSpectralMeasure U v)) :
    unitaryCyclicLpEquiv U v (spectralCoordinateUnitary (unitaryVectorSpectralMeasure U v) f) =
      cyclicRestriction U v (unitaryCyclicLpEquiv U v f) := by
  apply Subtype.ext
  change ((unitaryCyclicLpEquiv U v
    (spectralCoordinateUnitary (unitaryVectorSpectralMeasure U v) f) : cyclicSpan U v) : H) =
      U ((unitaryCyclicLpEquiv U v f : cyclicSpan U v) : H)
  rw [unitaryCyclicLpEquiv_coe, unitaryCyclicLpEquiv_coe]
  calc
    representationVectorLpIsometry (unitaryCircleRepresentation U) v
        (spectralCoordinateUnitary (unitaryVectorSpectralMeasure U v) f) =
      representationVectorLpIsometry (unitaryCircleRepresentation U) v
        (continuousMultiplierL2 (unitaryVectorSpectralMeasure U v) circleCoordinate f) := by
          rw [continuousMultiplierL2_phase (unitaryVectorSpectralMeasure U v)
            circleCoordinate circleCoordinate_norm f]
          rfl
    _ = unitaryCircleRepresentation U circleCoordinate
        (representationVectorLpIsometry (unitaryCircleRepresentation U) v f) :=
      representationVectorLpIsometry_intertwines (unitaryCircleRepresentation U) v circleCoordinate f
    _ = U (representationVectorLpIsometry (unitaryCircleRepresentation U) v f) := by
      rw [unitaryCircleRepresentation_coordinate]
      rfl

end
end OperatorCoding

end Source34

/- Preserved source skeleton: HilbertFamilyCongr -/
section Source35
/-! Actual coordinatewise unitary equivalences of countable Hilbert sums. -/

open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {I : Type*} {H G : I → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

def hilbertFamilyMap (e : ∀ i, H i ≃ₗᵢ[ℂ] G i) (x : lp H 2) : lp G 2 :=
  ⟨fun i => e i (x i), by
    apply memℓp_gen
    simpa only [LinearIsometryEquiv.norm_map] using
      (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)⟩

theorem hilbertFamilyMap_norm (e : ∀ i, H i ≃ₗᵢ[ℂ] G i) (x : lp H 2) :
    ‖hilbertFamilyMap e x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  apply tsum_congr
  intro i
  simp only [hilbertFamilyMap, LinearIsometryEquiv.norm_map]

def hilbertFamilyCongr (e : ∀ i, H i ≃ₗᵢ[ℂ] G i) : lp H 2 ≃ₗᵢ[ℂ] lp G 2 where
  toFun := hilbertFamilyMap e
  invFun := hilbertFamilyMap (fun i => (e i).symm)
  left_inv x := by
    apply lp.ext
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    apply lp.ext
    funext i
    exact (e i).apply_symm_apply (x i)
  map_add' x y := by
    apply lp.ext
    funext i
    exact (e i).map_add (x i) (y i)
  map_smul' c x := by
    apply lp.ext
    funext i
    exact (e i).map_smul c (x i)
  norm_map' := hilbertFamilyMap_norm e

theorem hilbertFamilyCongr_single [DecidableEq I]
    (e : ∀ i, H i ≃ₗᵢ[ℂ] G i) (i : I) (x : H i) :
    hilbertFamilyCongr e (lp.single 2 i x) = lp.single 2 i (e i x) := by
  apply lp.ext
  funext j
  by_cases hj : j = i
  · subst j
    simp [hilbertFamilyCongr, hilbertFamilyMap]
  · simp [hilbertFamilyCongr, hilbertFamilyMap, lp.single_apply, hj]

end
end MeasureUnitary

end Source35

/- Preserved source skeleton: UnitaryGreedyCyclicDecomposition -/
section Source36
/-! The actual Borel greedy cyclic generators obtained from a fixed
dense sequence by projecting away all earlier Laurent orbits. -/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H]

def greedyCyclicGenerator (U : StrongUnitary H) (n : ℕ) : H :=
  denseSeq H n - (closedFamilySpan (fun p : ℕ =>
    if hi : (Nat.unpair p).1 < n then
      (U ^ integerEnumeration (Nat.unpair p).2) (greedyCyclicGenerator U (Nat.unpair p).1)
    else 0)).starProjection (denseSeq H n)
termination_by n
decreasing_by exact hi

def greedyPreviousFamily (U : StrongUnitary H) (n : ℕ) (p : ℕ) : H :=
  if (Nat.unpair p).1 < n then
    (U ^ integerEnumeration (Nat.unpair p).2) (greedyCyclicGenerator U (Nat.unpair p).1)
  else 0

theorem greedyCyclicGenerator_formula (U : StrongUnitary H) (n : ℕ) :
    greedyCyclicGenerator U n = denseSeq H n -
      (closedFamilySpan (greedyPreviousFamily U n)).starProjection (denseSeq H n) := by
  conv_lhs => rw [greedyCyclicGenerator]
  rfl

theorem greedyCyclicGenerator_orthogonal_previous (U : StrongUnitary H) (n : ℕ) :
    greedyCyclicGenerator U n ∈ (closedFamilySpan (greedyPreviousFamily U n))ᗮ := by
  rw [greedyCyclicGenerator_formula]
  exact Submodule.sub_starProjection_mem_orthogonal _

theorem greedy_orbit_mem_previous (U : StrongUnitary H) (i n : ℕ) (hi : i < n) (m : ℤ) :
    (U ^ m) (greedyCyclicGenerator U i) ∈ closedFamilySpan (greedyPreviousFamily U n) := by
  obtain ⟨j,hj⟩ := integerEnumeration_surjective m
  apply Submodule.le_topologicalClosure _
  apply Submodule.subset_span
  refine ⟨Nat.pair i j, ?_⟩
  simp only [greedyPreviousFamily, Nat.unpair_pair, hi, if_pos, hj]

theorem greedy_cyclicSpan_le_previous (U : StrongUnitary H) (i n : ℕ) (hi : i < n) :
    cyclicSpan U (greedyCyclicGenerator U i) ≤ closedFamilySpan (greedyPreviousFamily U n) :=
  cyclicSpan_minimal U _ _ (Submodule.isClosed_topologicalClosure _)
    (fun m => greedy_orbit_mem_previous U i n hi m)

variable [MeasurableSpace H] [BorelSpace H]

local instance _root_.OperatorCoding.instMeasurableSpaceStrongUnitary_unitaryGreedyCyclicDecomposition : MeasurableSpace (StrongUnitary H) := borel _
local instance _root_.OperatorCoding.instBorelSpaceStrongUnitary_unitaryGreedyCyclicDecomposition : BorelSpace (StrongUnitary H) := ⟨rfl⟩

theorem greedyCyclicGenerator_measurable (n : ℕ) :
    Measurable (fun U : StrongUnitary H => greedyCyclicGenerator U n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hf (p : ℕ) : Measurable (fun U : StrongUnitary H => greedyPreviousFamily U n p) := by
      unfold greedyPreviousFamily
      split_ifs with hi
      · have heval : Continuous (fun q : StrongUnitary H × H => q.1 q.2) :=
          strongUnitary_continuous_action continuous_fst continuous_snd
        exact heval.measurable.comp
          ((continuous_id.zpow (integerEnumeration (Nat.unpair p).2)).measurable.prodMk
            (ih (Nat.unpair p).1 hi))
      · exact measurable_const
    have hp := closedFamilySpan_projection_measurable
      (fun U : StrongUnitary H => greedyPreviousFamily U n) hf
        (fun _ => denseSeq H n) measurable_const
    have heq : (fun U : StrongUnitary H => greedyCyclicGenerator U n) =
        (fun U : StrongUnitary H => denseSeq H n -
          (closedFamilySpan (greedyPreviousFamily U n)).starProjection (denseSeq H n)) :=
      funext (fun U => greedyCyclicGenerator_formula U n)
    rw [heq]
    exact measurable_const.sub hp

end
end OperatorCoding

end Source36

/- Preserved source skeleton: UnitaryGreedyCyclicCompleteness -/
section Source37
/-! The Borel greedy cyclic subspaces are pairwise orthogonal and span
the entire Hilbert space. Zero generators cause no exceptional case. -/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped InnerProductSpace

set_option maxHeartbeats 1500000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H]

def greedyCyclicAllSpan (U : StrongUnitary H) : Submodule ℂ H :=
  (⨆ n : ℕ, cyclicSpan U (greedyCyclicGenerator U n)).topologicalClosure

theorem greedy_previous_le_all (U : StrongUnitary H) (n : ℕ) :
    closedFamilySpan (greedyPreviousFamily U n) ≤ greedyCyclicAllSpan U := by
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro _ ⟨p,rfl⟩
  unfold greedyPreviousFamily
  split_ifs with hi
  · apply Submodule.le_topologicalClosure _
    apply le_iSup (fun i => cyclicSpan U (greedyCyclicGenerator U i)) (Nat.unpair p).1
    exact cyclicSpan_contains_orbit U (greedyCyclicGenerator U (Nat.unpair p).1)
      (integerEnumeration (Nat.unpair p).2)
  · exact Submodule.zero_mem _

theorem greedy_denseSeq_mem_all (U : StrongUnitary H) (n : ℕ) :
    denseSeq H n ∈ greedyCyclicAllSpan U := by
  have hg : greedyCyclicGenerator U n ∈ greedyCyclicAllSpan U :=
    Submodule.le_topologicalClosure _
      (le_iSup (fun i => cyclicSpan U (greedyCyclicGenerator U i)) n
        (cyclicSpan_contains_generator U (greedyCyclicGenerator U n)))
  have hp : (closedFamilySpan (greedyPreviousFamily U n)).starProjection (denseSeq H n) ∈
      greedyCyclicAllSpan U :=
    greedy_previous_le_all U n (Submodule.coe_mem
      ((closedFamilySpan (greedyPreviousFamily U n)).orthogonalProjection (denseSeq H n)))
  rw [greedyCyclicGenerator_formula] at hg
  simpa only [sub_add_cancel] using (greedyCyclicAllSpan U).add_mem hg hp

theorem greedyCyclicAllSpan_eq_top (U : StrongUnitary H) : greedyCyclicAllSpan U = ⊤ := by
  apply top_unique
  intro x hx
  have hrange : Set.range (denseSeq H) ⊆ (greedyCyclicAllSpan U : Set H) := by
    rintro _ ⟨n,rfl⟩
    exact greedy_denseSeq_mem_all U n
  have hclosed : IsClosed (greedyCyclicAllSpan U : Set H) := Submodule.isClosed_topologicalClosure _
  exact (closure_minimal hrange hclosed) (denseRange_denseSeq H x)

theorem greedy_cyclicSpans_isOrtho_of_lt (U : StrongUnitary H) (i j : ℕ) (hij : i < j) :
    (cyclicSpan U (greedyCyclicGenerator U i)).IsOrtho
      (cyclicSpan U (greedyCyclicGenerator U j)) := by
  have hj : greedyCyclicGenerator U j ∈ (cyclicSpan U (greedyCyclicGenerator U i))ᗮ :=
    Submodule.orthogonal_le (greedy_cyclicSpan_le_previous U i j hij)
      (greedyCyclicGenerator_orthogonal_previous U j)
  have hle : cyclicSpan U (greedyCyclicGenerator U j) ≤
      (cyclicSpan U (greedyCyclicGenerator U i))ᗮ :=
    cyclicSpan_minimal U _ _ (Submodule.isClosed_orthogonal _)
      (fun m => cyclicSpan_orthogonal_zpow_invariant U (greedyCyclicGenerator U i) m
        (greedyCyclicGenerator U j) hj)
  exact (Submodule.isOrtho_iff_le.mpr hle).symm

theorem greedy_cyclicSpans_pairwise_isOrtho (U : StrongUnitary H) :
    Pairwise (fun i j => (cyclicSpan U (greedyCyclicGenerator U i)).IsOrtho
      (cyclicSpan U (greedyCyclicGenerator U j))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact greedy_cyclicSpans_isOrtho_of_lt U i j hlt
  · exact (greedy_cyclicSpans_isOrtho_of_lt U j i hgt).symm

end
end OperatorCoding

end Source37

/- Preserved source skeleton: UnitaryGreedyHilbertSum -/
section Source38
/-! The actual unitary identification of the original Hilbert space
with the countable Hilbert sum of its Borel greedy cyclic subspaces. -/

open MeasureTheory Set
open scoped InnerProductSpace

set_option maxHeartbeats 1000000

namespace OperatorCoding

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [SecondCountableTopology H]

def greedyCyclicHilbertSum (U : StrongUnitary H) :
    IsHilbertSum ℂ (fun n : ℕ => cyclicSpan U (greedyCyclicGenerator U n))
      (fun n => (cyclicSpan U (greedyCyclicGenerator U n)).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal
  · intro i j hij x y
    exact (greedy_cyclicSpans_pairwise_isOrtho U hij).inner_eq x.property y.property
  · change ⊤ ≤ greedyCyclicAllSpan U
    rw [greedyCyclicAllSpan_eq_top]

def greedyCyclicCoordinates (U : StrongUnitary H) :
    H ≃ₗᵢ[ℂ] lp (fun n : ℕ => cyclicSpan U (greedyCyclicGenerator U n)) 2 :=
  (greedyCyclicHilbertSum U).linearIsometryEquiv

theorem greedyCyclicCoordinates_symm_single (U : StrongUnitary H) (n : ℕ)
    (x : cyclicSpan U (greedyCyclicGenerator U n)) :
    (greedyCyclicCoordinates U).symm (lp.single 2 n x) = (x : H) :=
  (greedyCyclicHilbertSum U).linearIsometryEquiv_symm_apply_single x

end
end OperatorCoding

end Source38

/- Preserved source skeleton: UnitaryFullSpectralModel -/
section Source39
/-! The actual countable cyclic spectral model of an arbitrary unitary,
using its Borel greedy cyclic vector measures on one fixed circle. -/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 2000000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

def greedySpectralMeasure (U : StrongUnitary H) (n : ℕ) : Measure SpectralCircle :=
  unitaryVectorSpectralMeasure U (greedyCyclicGenerator U n)

instance greedySpectralMeasure_finite (U : StrongUnitary H) (n : ℕ) :
    IsFiniteMeasure (greedySpectralMeasure U n) := by
  unfold greedySpectralMeasure
  infer_instance

abbrev UnitarySpectralSum (U : StrongUnitary H) :=
  lp (fun n : ℕ => Lp ℂ 2 (greedySpectralMeasure U n)) 2

def unitarySpectralSumEquiv (U : StrongUnitary H) : UnitarySpectralSum U ≃ₗᵢ[ℂ] H :=
  (hilbertFamilyCongr (fun n => unitaryCyclicLpEquiv U (greedyCyclicGenerator U n))).trans
    (greedyCyclicCoordinates U).symm

def spectralSumUnitary (U : StrongUnitary H) : StrongUnitary (UnitarySpectralSum U) :=
  hilbertFamilyCongr (fun n => spectralCoordinateUnitary (greedySpectralMeasure U n))

theorem unitarySpectralSumEquiv_single (U : StrongUnitary H) (n : ℕ)
    (f : Lp ℂ 2 (greedySpectralMeasure U n)) :
    unitarySpectralSumEquiv U (lp.single 2 n f) =
      ((unitaryCyclicLpEquiv U (greedyCyclicGenerator U n) f :
        cyclicSpan U (greedyCyclicGenerator U n)) : H) := by
  change (greedyCyclicCoordinates U).symm
    (hilbertFamilyCongr (fun i => unitaryCyclicLpEquiv U (greedyCyclicGenerator U i))
      (lp.single 2 n f)) = _
  rw [hilbertFamilyCongr_single, greedyCyclicCoordinates_symm_single]

theorem spectralSumUnitary_single (U : StrongUnitary H) (n : ℕ)
    (f : Lp ℂ 2 (greedySpectralMeasure U n)) :
    spectralSumUnitary U (lp.single 2 n f) =
      lp.single 2 n (spectralCoordinateUnitary (greedySpectralMeasure U n) f) := by
  exact hilbertFamilyCongr_single
    (fun i : ℕ => spectralCoordinateUnitary (greedySpectralMeasure U i)) n f

theorem unitarySpectralSumEquiv_intertwines (U : StrongUnitary H)
    (f : UnitarySpectralSum U) :
    unitarySpectralSumEquiv U (spectralSumUnitary U f) = U (unitarySpectralSumEquiv U f) := by
  have hmaps :
      (unitarySpectralSumEquiv U).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (spectralSumUnitary U).toContinuousLinearEquiv.toContinuousLinearMap =
      (U : H →L[ℂ] H).comp (unitarySpectralSumEquiv U).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    intro n
    apply ContinuousLinearMap.ext
    intro g
    change unitarySpectralSumEquiv U (spectralSumUnitary U (lp.single 2 n g)) =
      U (unitarySpectralSumEquiv U (lp.single 2 n g))
    rw [spectralSumUnitary_single, unitarySpectralSumEquiv_single, unitarySpectralSumEquiv_single]
    exact congrArg (fun z : cyclicSpan U (greedyCyclicGenerator U n) => (z : H))
      (unitaryCyclicLpEquiv_intertwines U (greedyCyclicGenerator U n) g)
  exact congrArg (fun T => T f) hmaps

end
end OperatorCoding

end Source39

/- Preserved source skeleton: UnitarySpectralMeasureBorel -/
section Source40
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

set_option maxHeartbeats 1500000

noncomputable section

namespace OperatorCoding

open MeasureUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

local instance _root_.OperatorCoding.instMeasurableSpace_unitarySpectralMeasureBorel : MeasurableSpace H := borel _
local instance _root_.OperatorCoding.instBorelSpace_unitarySpectralMeasureBorel : BorelSpace H := ⟨rfl⟩
local instance _root_.OperatorCoding.instMeasurableSpaceStrongUnitary_unitarySpectralMeasureBorel : MeasurableSpace (StrongUnitary H) := borel _
local instance _root_.OperatorCoding.instBorelSpaceStrongUnitary_unitarySpectralMeasureBorel : BorelSpace (StrongUnitary H) := ⟨rfl⟩

theorem unitaryVectorSpectralMeasure_realTest_continuous (f : C(SpectralCircle, ℝ)) :
    Continuous (fun p : StrongUnitary H × H => ∫ x, f x ∂unitaryVectorSpectralMeasure p.1 p.2) := by
  let fc := realContinuousCompactSupport f
  have he := unitaryCircleRepresentation_joint_continuous (H := H) (complexifyCompactSupport fc)
  have hc : Continuous (fun p : StrongUnitary H × H =>
      (inner ℂ p.2 (unitaryCircleRepresentation p.1 (complexifyCompactSupport fc) p.2)).re) :=
    Complex.continuous_re.comp (continuous_snd.inner (𝕜 := ℂ) he)
  convert hc using 1
  funext p
  exact representationVectorMeasure_integral (unitaryCircleRepresentation p.1) p.2 fc

theorem unitaryVectorSpectralMeasure_nnTest_measurable (f : SpectralCircle →ᵇ ℝ≥0) :
    Measurable (fun p : StrongUnitary H × H =>
      ∫⁻ x, (f x : ℝ≥0∞) ∂unitaryVectorSpectralMeasure p.1 p.2) := by
  let g : C(SpectralCircle, ℝ) :=
    ⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩
  have he : (fun p : StrongUnitary H × H =>
      ∫⁻ x, (f x : ℝ≥0∞) ∂unitaryVectorSpectralMeasure p.1 p.2) =
      (fun p => ENNReal.ofReal (∫ x, g x ∂unitaryVectorSpectralMeasure p.1 p.2)) := by
    funext p
    have hi : Integrable g (unitaryVectorSpectralMeasure p.1 p.2) :=
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simpa only [g,ContinuousMap.coe_mk,ENNReal.ofReal_coe_nnreal] using
      (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
        (fun x => NNReal.coe_nonneg (f x)))).symm
  rw [he]
  exact (unitaryVectorSpectralMeasure_realTest_continuous g).measurable.ennreal_ofReal

theorem unitaryVectorSpectralMeasure_closed_measurable (F : Set SpectralCircle) (hF : IsClosed F) :
    Measurable (fun p : StrongUnitary H × H => unitaryVectorSpectralMeasure p.1 p.2 F) := by
  have hlim : Tendsto (fun n (p : StrongUnitary H × H) =>
      ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂unitaryVectorSpectralMeasure p.1 p.2) atTop
      (𝓝 (fun p => unitaryVectorSpectralMeasure p.1 p.2 F)) := by
    apply tendsto_pi_nhds.mpr
    intro p
    exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (unitaryVectorSpectralMeasure p.1 p.2)
  exact measurable_of_tendsto_metrizable
    (fun n => unitaryVectorSpectralMeasure_nnTest_measurable (hF.apprSeq n)) hlim

theorem unitaryVectorSpectralMeasure_measurable :
    Measurable (fun p : StrongUnitary H × H => unitaryVectorSpectralMeasure p.1 p.2) := by
  have hgen : (inferInstance : MeasurableSpace SpectralCircle) =
      MeasurableSpace.generateFrom {s : Set SpectralCircle | IsClosed s} :=
    (BorelSpace.measurable_eq : (inferInstance : MeasurableSpace SpectralCircle) =
      borel SpectralCircle).trans borel_eq_generateFrom_isClosed
  apply Measurable.measure_of_isPiSystem (S := {s : Set SpectralCircle | IsClosed s})
  · exact hgen
  · exact isPiSystem_isClosed
  · intro F hF
    exact unitaryVectorSpectralMeasure_closed_measurable F hF
  · exact unitaryVectorSpectralMeasure_closed_measurable univ isClosed_univ

theorem greedySpectralMeasure_measurable (n : ℕ) :
    Measurable (fun U : StrongUnitary H => greedySpectralMeasure U n) := by
  change Measurable ((fun p : StrongUnitary H × H => unitaryVectorSpectralMeasure p.1 p.2) ∘
    (fun U : StrongUnitary H => (U,greedyCyclicGenerator U n)))
  exact (unitaryVectorSpectralMeasure_measurable (H := H)).comp
    (measurable_id.prodMk (greedyCyclicGenerator_measurable (H := H) n))

end OperatorCoding

end
end Source40

/- Preserved source skeleton: UnitaryMeasurableSpectralSupports -/
section Source41
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

namespace OperatorCoding

open MeasureUnitary SpectralDomination

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

local instance _root_.OperatorCoding.instMeasurableSpace_unitaryMeasurableSpectralSupports : MeasurableSpace H := borel _
local instance _root_.OperatorCoding.instBorelSpace_unitaryMeasurableSpectralSupports : BorelSpace H := ⟨rfl⟩
local instance _root_.OperatorCoding.instMeasurableSpaceStrongUnitary_unitaryMeasurableSpectralSupports : MeasurableSpace (StrongUnitary H) := borel _
local instance _root_.OperatorCoding.instBorelSpaceStrongUnitary_unitaryMeasurableSpectralSupports : BorelSpace (StrongUnitary H) := ⟨rfl⟩

def spectralBasePoint : SpectralCircle := ⟨1, by simp⟩

def greedyWeightedKernel (n : ℕ) : Kernel (StrongUnitary H) SpectralCircle :=
  weightedKernel (fun U n => greedySpectralMeasure U n) greedySpectralMeasure_measurable n

def greedyDominatingKernel : Kernel (StrongUnitary H) SpectralCircle :=
  dominatingKernel (fun U n => greedySpectralMeasure U n) greedySpectralMeasure_measurable spectralBasePoint

instance greedyWeightedKernel_finite (n : ℕ) : IsFiniteKernel (greedyWeightedKernel (H := H) n) := by
  unfold greedyWeightedKernel
  infer_instance

instance greedyDominatingKernel_finite : IsFiniteKernel (greedyDominatingKernel (H := H)) := by
  unfold greedyDominatingKernel
  infer_instance

def greedySpectralSupport (U : StrongUnitary H) (n : ℕ) : Set SpectralCircle :=
  kernelSupport (greedyWeightedKernel n) greedyDominatingKernel U

theorem greedySpectralSupport_measurableSet (U : StrongUnitary H) (n : ℕ) :
    MeasurableSet (greedySpectralSupport U n) :=
  measurableSet_kernelSupport _ _ _

theorem greedySpectralSupport_joint_measurableSet (n : ℕ) :
    MeasurableSet {p : StrongUnitary H × SpectralCircle | p.2 ∈ greedySpectralSupport p.1 n} :=
  measurableSet_kernelSupport_joint _ _

theorem greedyWeightedKernel_ac_dominating (U : StrongUnitary H) (n : ℕ) :
    greedyWeightedKernel n U ≪ greedyDominatingKernel U := by
  change weight (fun n => greedySpectralMeasure U n) n • greedySpectralMeasure U n ≪ _
  exact (measure_ac_dominatingKernel (fun V n => greedySpectralMeasure V n)
    greedySpectralMeasure_measurable spectralBasePoint U n).smul_left _

theorem greedySpectralSupport_equivalent (U : StrongUnitary H) (n : ℕ) :
    greedySpectralMeasure U n ≪ (greedyDominatingKernel U).restrict (greedySpectralSupport U n) ∧
      (greedyDominatingKernel U).restrict (greedySpectralSupport U n) ≪ greedySpectralMeasure U n := by
  have h := kernel_support_equivalent (greedyWeightedKernel n) greedyDominatingKernel U
    (greedyWeightedKernel_ac_dominating U n)
  have hscale : greedySpectralMeasure U n ≪ greedyWeightedKernel n U :=
    Measure.absolutelyContinuous_smul (weight_ne_zero (greedySpectralMeasure U) n)
  exact ⟨hscale.trans h.1, h.2.trans Measure.smul_absolutelyContinuous⟩

end OperatorCoding

end
end Source41

/- Preserved source skeleton: FiberMultiplicityOperators -/
section Source42
/-! Actual ambient operators and Parseval identities obtained from a
unitary between measurable finite-base/counting-fiber L² subspaces. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureUnitary

open MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Restriction

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def measureFiberSet (A : ℕ → Set X) : Set (X × ℕ) := {p | p.1 ∈ A p.2}

theorem measureFiberSet_measurable (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    MeasurableSet (measureFiberSet A) := by
  have heq : measureFiberSet A = ⋃ i : ℕ, A i ×ˢ {i} := by
    ext p
    simp only [measureFiberSet, mem_setOf_eq, mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨p.2,hp,rfl⟩
    · rintro ⟨i,hp,hi⟩
      simpa only [hi] using hp
  rw [heq]
  exact MeasurableSet.iUnion (fun i => (hA i).prod (measurableSet_singleton i))

abbrev fiberAmbientMeasure := μ.prod (Measure.count : Measure ℕ)
abbrev fiberRestrictedMeasure (A : ℕ → Set X) := (fiberAmbientMeasure μ).restrict (measureFiberSet A)

def fiberGlobalOperator (A B : ℕ → Set X) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B)) :
    Lp ℂ 2 (fiberAmbientMeasure μ) →L[ℂ] Lp ℂ 2 (fiberAmbientMeasure μ) :=
  globalizeOperator (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet B)
    (measureFiberSet_measurable B hB) U.toContinuousLinearEquiv.toContinuousLinearMap

theorem fiberGlobalOperator_adjoint (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B)) :
    (fiberGlobalOperator μ A B hB U).adjoint = fiberGlobalOperator μ B A hA U.symm := by
  rw [fiberGlobalOperator, globalize_adjoint _ _ _ (measureFiberSet_measurable A hA), U.adjoint_eq_symm]
  rfl

theorem fiberGlobalOperator_norm (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (f : Lp ℂ 2 (fiberAmbientMeasure μ)) :
    ‖fiberGlobalOperator μ A B hB U f‖ =
      ‖indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA) f‖ := by
  change ‖zeroExtend (fiberAmbientMeasure μ) (measureFiberSet B)
    (measureFiberSet_measurable B hB)
    (U (restrictMap (fiberAmbientMeasure μ) (measureFiberSet A) f))‖ = _
  rw [zeroExtend_norm, U.norm_map, ← zeroExtend_norm (fiberAmbientMeasure μ)
    (measureFiberSet A) (measureFiberSet_measurable A hA), zeroExtend_restrict]

theorem fiber_injection_indicator (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (e : ℕ) (f : Lp ℂ 2 μ) :
    injection μ e (indicatorL2 μ (hA e) f) =
      indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA) (injection μ e f) :=
  injection_indicator μ id measurable_id (measureFiberSet A) (measureFiberSet_measurable A hA) e f

theorem fiberGlobalOperator_column_norm_sq (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (e : ℕ) (f : Lp ℂ 2 μ) :
    (∑' d : ℕ, ‖matrixCoefficient μ μ (fiberGlobalOperator μ A B hB U) d e f‖ ^ 2) =
      ‖indicatorL2 μ (hA e) f‖ ^ 2 := by
  change (∑' d : ℕ, ‖coefficient μ d
    (fiberGlobalOperator μ A B hB U (injection μ e f))‖ ^ 2) = _
  rw [← norm_sq_eq_tsum_coefficient_norm_sq, fiberGlobalOperator_norm μ A B hA hB U,
    ← fiber_injection_indicator μ A hA e f, injection_norm]

theorem fiberGlobalOperator_commutes_base_projections (A B : ℕ → Set X)
    (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (hU : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)),
      U (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) (U f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberAmbientMeasure μ)) :
    fiberGlobalOperator μ A B hB U
      (indicatorL2 (fiberAmbientMeasure μ) (hs.preimage measurable_fst) f) =
      indicatorL2 (fiberAmbientMeasure μ) (hs.preimage measurable_fst)
        (fiberGlobalOperator μ A B hB U f) := by
  change zeroExtend (fiberAmbientMeasure μ) (measureFiberSet B) (measureFiberSet_measurable B hB)
    (U (restrictMap (fiberAmbientMeasure μ) (measureFiberSet A)
      (indicatorL2 (fiberAmbientMeasure μ) (hs.preimage measurable_fst) f))) = _
  rw [restrict_indicator, hU s hs, zeroExtend_indicator]
  rfl

end
end MeasureUnitary

end Source42

/- Preserved source skeleton: L2ModuleEntryMass -/
section Source43
/-! Pointwise squared-mass identities of actual finite-base L² module
operators, obtained from their localized Parseval identities. -/

open MeasureTheory Filter Set
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def moduleEntryMass (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (‖T (constantOneL2 μ) x‖ ^ 2)

theorem moduleEntryMass_measurable (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Measurable (moduleEntryMass μ T) :=
  (((Lp.stronglyMeasurable (T (constantOneL2 μ))).measurable.norm).pow_const 2).ennreal_ofReal

theorem moduleEntryMass_setLIntegral (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (s : Set X) (hs : MeasurableSet s) :
    (∫⁻ x in s, moduleEntryMass μ T x ∂μ) =
      ENNReal.ofReal (‖indicatorL2 μ hs (T (constantOneL2 μ))‖ ^ 2) := by
  rw [← vectorDensityMeasure_apply μ hs (T (constantOneL2 μ))]
  exact (withDensity_apply _ hs).symm

theorem moduleEntryMass_adjoint_ae_eq (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    moduleEntryMass μ T =ᵐ[μ] moduleEntryMass μ T.adjoint := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (moduleEntryMass_measurable μ T) (moduleEntryMass_measurable μ T.adjoint)
  intro s hs _hfin
  rw [moduleEntryMass_setLIntegral μ T s hs, moduleEntryMass_setLIntegral μ T.adjoint s hs,
    ← hT s hs, ← projectionCommutant_adjoint μ T hT s hs,
    projectionCommutant_norm_adjoint μ T hT]

theorem indicatorL2_commute (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : Lp ℂ 2 μ) :
    indicatorL2 μ hs (indicatorL2 μ ht f) = indicatorL2 μ ht (indicatorL2 μ hs f) := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ hs (indicatorL2 μ ht f), indicatorL2_coe μ ht f,
    indicatorL2_coe μ ht (indicatorL2 μ hs f), indicatorL2_coe μ hs f]
      with x hst ht' hts hs'
  rw [hst, hts]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs,hxt,ht',hs']

theorem indicatorOne_squareMass (A : Set X) (hA : MeasurableSet A) :
    (fun x => ENNReal.ofReal (‖indicatorL2 μ hA (constantOneL2 μ) x‖ ^ 2)) =ᵐ[μ]
      A.indicator (fun _ => (1 : ℝ≥0∞)) := by
  filter_upwards [indicatorL2_coe μ hA (constantOneL2 μ), constantOneL2_coe μ] with x hi h1
  rw [hi]
  by_cases hx : x ∈ A <;> simp [hx,h1]

theorem module_column_mass_ae_eq
    (T : ℕ → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ d (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T d (indicatorL2 μ hs f) = indicatorL2 μ hs (T d f))
    (A : Set X) (hA : MeasurableSet A)
    (hsum : ∀ f : Lp ℂ 2 μ, Summable (fun d => ‖T d f‖ ^ 2))
    (hnorm : ∀ f : Lp ℂ 2 μ, (∑' d, ‖T d f‖ ^ 2) = ‖indicatorL2 μ hA f‖ ^ 2) :
    (fun x => ∑' d : ℕ, moduleEntryMass μ (T d) x) =ᵐ[μ]
      A.indicator (fun _ => (1 : ℝ≥0∞)) := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Measurable.ennreal_tsum (fun d => moduleEntryMass_measurable μ (T d)))
    (measurable_const.indicator hA)
  intro s hs _hfin
  calc
    (∫⁻ x in s, ∑' d : ℕ, moduleEntryMass μ (T d) x ∂μ) =
        ∑' d : ℕ, ∫⁻ x in s, moduleEntryMass μ (T d) x ∂μ :=
      lintegral_tsum (fun d => (moduleEntryMass_measurable μ (T d)).aemeasurable)
    _ = ∑' d : ℕ, ENNReal.ofReal (‖T d (indicatorL2 μ hs (constantOneL2 μ))‖ ^ 2) := by
      apply tsum_congr
      intro d
      rw [moduleEntryMass_setLIntegral μ (T d) s hs, ← hT d s hs]
    _ = ENNReal.ofReal (∑' d : ℕ, ‖T d (indicatorL2 μ hs (constantOneL2 μ))‖ ^ 2) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hsum _)).symm
    _ = ENNReal.ofReal (‖indicatorL2 μ hA (indicatorL2 μ hs (constantOneL2 μ))‖ ^ 2) := by rw [hnorm]
    _ = ENNReal.ofReal (‖indicatorL2 μ hs (indicatorL2 μ hA (constantOneL2 μ))‖ ^ 2) := by
      rw [indicatorL2_commute]
    _ = ∫⁻ x in s, ENNReal.ofReal (‖indicatorL2 μ hA (constantOneL2 μ) x‖ ^ 2) ∂μ := by
      rw [← vectorDensityMeasure_apply μ hs]
      exact withDensity_apply _ hs
    _ = ∫⁻ x in s, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
      lintegral_congr_ae (ae_restrict_of_ae (indicatorOne_squareMass μ A hA))

end
end MeasureUnitary

end Source43

/- Preserved source skeleton: FiberMultiplicityReflection -/
section Source44
/-! Actual base-projection intertwiners preserve pointwise Hilbert-fiber
multiplicity. Parseval and adjoint transposition supply both stochastic
matrix identities; no matrix or dimension hypothesis is postulated. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace MeasureUnitary

open MeasureEquivalenceL2Coefficients

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def fiberMultiplicity (A : ℕ → Set X) (x : X) : ℝ≥0∞ :=
  ∑' i : ℕ, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x

theorem fiberMultiplicity_measurable (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (fiberMultiplicity A) :=
  Measurable.ennreal_tsum (fun i => measurable_const.indicator (hA i))

theorem fiberMatrixCoefficient_commutes (A B : ℕ → Set X)
    (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (hU : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)),
      U (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) (U f))
    (d e : ℕ) (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    matrixCoefficient μ μ (fiberGlobalOperator μ A B hB U) d e (indicatorL2 μ hs f) =
      indicatorL2 μ hs (matrixCoefficient μ μ (fiberGlobalOperator μ A B hB U) d e f) :=
  matrixCoefficient_intertwines_projections μ μ Prod.fst Prod.fst measurable_fst measurable_fst
    (fiberGlobalOperator μ A B hB U) (fiberGlobalOperator_commutes_base_projections μ A B hB U hU)
      s hs d e f

theorem fiberMultiplicity_eq_of_intertwiner
    (A B : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (U : Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B))
    (hU : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)),
      U (indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) (U f)) :
    fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B := by
  let T := fiberGlobalOperator μ A B hB U
  let V := fiberGlobalOperator μ B A hA U.symm
  have hInv : ∀ (s : Set X) (hs : MeasurableSet s)
      (f : Lp ℂ 2 (fiberRestrictedMeasure μ B)),
      U.symm (indicatorL2 (fiberRestrictedMeasure μ B) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure μ A) (hs.preimage measurable_fst) (U.symm f) := by
    intro s hs f
    apply U.injective
    rw [LinearIsometryEquiv.apply_symm_apply, hU s hs, LinearIsometryEquiv.apply_symm_apply]
  have hcol (e : ℕ) : (fun x => ∑' d : ℕ,
      moduleEntryMass μ (matrixCoefficient μ μ T d e) x) =ᵐ[μ]
      (A e).indicator (fun _ => (1 : ℝ≥0∞)) := by
    apply module_column_mass_ae_eq μ (fun d => matrixCoefficient μ μ T d e)
      (fun d => fiberMatrixCoefficient_commutes μ A B hB U hU d e) (A e) (hA e)
    · intro f
      exact summable_coefficient_norm_sq μ (T (injection μ e f))
    · exact fiberGlobalOperator_column_norm_sq μ A B hA hB U e
  have hcolV (d : ℕ) : (fun x => ∑' e : ℕ,
      moduleEntryMass μ (matrixCoefficient μ μ V e d) x) =ᵐ[μ]
      (B d).indicator (fun _ => (1 : ℝ≥0∞)) := by
    apply module_column_mass_ae_eq μ (fun e => matrixCoefficient μ μ V e d)
      (fun e => fiberMatrixCoefficient_commutes μ B A hA U.symm hInv e d) (B d) (hB d)
    · intro f
      exact summable_coefficient_norm_sq μ (V (injection μ d f))
    · exact fiberGlobalOperator_column_norm_sq μ B A hB hA U.symm d
  have hentry (d e : ℕ) : moduleEntryMass μ (matrixCoefficient μ μ T d e) =ᵐ[μ]
      moduleEntryMass μ (matrixCoefficient μ μ V e d) := by
    have h := moduleEntryMass_adjoint_ae_eq μ (matrixCoefficient μ μ T d e)
      (fiberMatrixCoefficient_commutes μ A B hB U hU d e)
    rw [matrixCoefficient_adjoint] at h
    have hAdj : T.adjoint = V := fiberGlobalOperator_adjoint μ A B hA hB U
    rw [hAdj] at h
    exact h
  have hrow (d : ℕ) : (fun x => ∑' e : ℕ,
      moduleEntryMass μ (matrixCoefficient μ μ T d e) x) =ᵐ[μ]
      (B d).indicator (fun _ => (1 : ℝ≥0∞)) := by
    filter_upwards [ae_all_iff.mpr (fun e => hentry d e), hcolV d] with x hx hv
    exact (tsum_congr (fun e => hx e)).trans hv
  filter_upwards [ae_all_iff.mpr hcol, ae_all_iff.mpr hrow] with x hc hr
  change (∑' e : ℕ, (A e).indicator (fun _ => (1 : ℝ≥0∞)) x) =
    ∑' d : ℕ, (B d).indicator (fun _ => (1 : ℝ≥0∞)) x
  calc
    (∑' e : ℕ, (A e).indicator (fun _ => (1 : ℝ≥0∞)) x) =
        ∑' e : ℕ, ∑' d : ℕ, moduleEntryMass μ (matrixCoefficient μ μ T d e) x :=
      tsum_congr (fun e => (hc e).symm)
    _ = ∑' d : ℕ, ∑' e : ℕ, moduleEntryMass μ (matrixCoefficient μ μ T d e) x := ENNReal.tsum_comm
    _ = ∑' d : ℕ, (B d).indicator (fun _ => (1 : ℝ≥0∞)) x := tsum_congr hr

end
end MeasureUnitary

end Source44

/- Preserved source skeleton: MeasurableNthTotal -/
section Source45
/-! The total Nat.nth selector is Borel for arbitrary Borel predicates,
including finite and empty fibers. Out-of-range indices return zero. -/

open MeasureTheory Set

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem measurable_nat_nth_total (p : X → ℕ → Prop) [∀ x, DecidablePred (p x)]
    (hp : ∀ n, MeasurableSet {x | p x n}) (n : ℕ) :
    Measurable (fun x => Nat.nth (p x) n) := by
  have hnonzero (m : ℕ) (hm : m ≠ 0) :
      {x | Nat.nth (p x) n = m} = {x | p x m} ∩ {x | Nat.count (p x) m = n} := by
    ext x
    constructor
    · intro he
      have hne : Nat.nth (p x) n ≠ 0 := fun hz => hm (he.symm.trans hz)
      have hcard : ∀ hf : {k : ℕ | p x k}.Finite, n < hf.toFinset.card :=
        fun hf => Nat.lt_card_toFinset_of_nth_ne_zero hne hf
      exact ⟨he ▸ Nat.nth_mem n hcard, he ▸ Nat.count_nth hcard⟩
    · rintro ⟨hpm,hcount⟩
      rw [← hcount]
      exact Nat.nth_count hpm
  have hmeas (m : ℕ) (hm : m ≠ 0) : MeasurableSet {x | Nat.nth (p x) n = m} := by
    rw [hnonzero m hm]
    exact (hp m).inter (measurableSet_eq_fun (measurable_nat_count p hp m) measurable_const)
  apply measurable_to_countable'
  intro m
  by_cases hm : m = 0
  · subst m
    have heq : {x | Nat.nth (p x) n = 0} =
        (⋃ k : {i : ℕ // i ≠ 0}, {x | Nat.nth (p x) n = k.val})ᶜ := by
      ext x
      simp only [mem_setOf_eq, mem_compl_iff, mem_iUnion]
      constructor
      · intro hx
        rintro ⟨k,hk⟩
        exact k.property (hk.symm.trans hx)
      · intro hx
        by_contra hne
        exact hx ⟨⟨Nat.nth (p x) n,hne⟩,rfl⟩
    change MeasurableSet {x | Nat.nth (p x) n = 0}
    rw [heq]
    exact (MeasurableSet.iUnion (fun k : {i : ℕ // i ≠ 0} => hmeas k.val k.property)).compl
  · exact hmeas m hm

end
end MeasureUnitary

end Source45

/- Preserved source skeleton: FiberMultiplicityMatching -/
section Source46
/-! A canonical Borel matching between equal-multiplicity counting
fibers, obtained by matching the preceding active-index counts. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem fiberMultiplicity_eq_encard (A : ℕ → Set X) (x : X) :
    fiberMultiplicity A x = (({i : ℕ | x ∈ A i}.encard : ℕ∞) : ℝ≥0∞) := by
  unfold fiberMultiplicity
  rw [← ENNReal.tsum_set_one {i : ℕ | x ∈ A i},
    tsum_subtype {i : ℕ | x ∈ A i} (fun _ : ℕ => (1 : ℝ≥0∞))]
  apply tsum_congr
  intro i
  by_cases hi : x ∈ A i <;> simp [hi]

theorem nth_count_other_of_encard_eq (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (hcard : {i : ℕ | p i}.encard = {i : ℕ | q i}.encard) (i : ℕ) (hpi : p i) :
    q (Nat.nth q (Nat.count p i)) ∧ Nat.count q (Nat.nth q (Nat.count p i)) = Nat.count p i := by
  have henough : ∀ hq : {i : ℕ | q i}.Finite, Nat.count p i < hq.toFinset.card := by
    intro hq
    have hp : {i : ℕ | p i}.Finite := (Set.finite_iff_finite_of_encard_eq_encard hcard).mpr hq
    have hnat : hp.toFinset.card = hq.toFinset.card := by
      have h := hcard
      rw [hp.encard_eq_coe_toFinset_card, hq.encard_eq_coe_toFinset_card] at h
      exact_mod_cast h
    rw [← hnat]
    exact Nat.count_lt_card hp hpi
  exact ⟨Nat.nth_mem _ henough, Nat.count_nth henough⟩

def fiberNthMatch (A B : ℕ → Set X) (p : X × ℕ) : X × ℕ := by
  classical
  exact (p.1, Nat.nth (fun j => p.1 ∈ B j) (Nat.count (fun i => p.1 ∈ A i) p.2))



theorem fiberNthMatch_measurable (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (fiberNthMatch A B) := by
  classical
  have hcount : Measurable (fun p : X × ℕ => Nat.count (fun i => p.1 ∈ A i) p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_nat_count (fun x j => x ∈ A j) hA i)
  have hnth : Measurable (fun p : X × ℕ => Nat.nth (fun i => p.1 ∈ B i) p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_nat_nth_total (fun x j => x ∈ B j) hB i)
  exact measurable_fst.prodMk (hnth.comp (measurable_fst.prodMk hcount))

theorem fiberNthMatch_mem (A B : ℕ → Set X) (x : X)
    (hcard : fiberMultiplicity A x = fiberMultiplicity B x) (i : ℕ) (hi : x ∈ A i) :
    fiberNthMatch A B (x,i) ∈ measureFiberSet B := by
  classical
  have hc : {j : ℕ | x ∈ A j}.encard = {j : ℕ | x ∈ B j}.encard := by
    rw [fiberMultiplicity_eq_encard, fiberMultiplicity_eq_encard] at hcard
    exact ENat.toENNReal_inj.mp hcard
  exact (nth_count_other_of_encard_eq (fun j => x ∈ A j) (fun j => x ∈ B j) hc i hi).1

theorem fiberNthMatch_inverse (A B : ℕ → Set X) (x : X)
    (hcard : fiberMultiplicity A x = fiberMultiplicity B x) (i : ℕ) (hi : x ∈ A i) :
    fiberNthMatch B A (fiberNthMatch A B (x,i)) = (x,i) := by
  classical
  have hc : {j : ℕ | x ∈ A j}.encard = {j : ℕ | x ∈ B j}.encard := by
    rw [fiberMultiplicity_eq_encard, fiberMultiplicity_eq_encard] at hcard
    exact ENat.toENNReal_inj.mp hcard
  have hmatch := nth_count_other_of_encard_eq (fun j => x ∈ A j) (fun j => x ∈ B j) hc i hi
  apply Prod.ext
  · rfl
  · change Nat.nth (fun j => x ∈ A j)
      (Nat.count (fun j => x ∈ B j) (Nat.nth (fun j => x ∈ B j) (Nat.count (fun j => x ∈ A j) i))) = i
    rw [hmatch.2]
    exact Nat.nth_count hi

def fiberActiveEquiv (A B : ℕ → Set X) (x : X)
    (hcard : fiberMultiplicity A x = fiberMultiplicity B x) :
    {i : ℕ | x ∈ A i} ≃ {j : ℕ | x ∈ B j} where
  toFun i := ⟨(fiberNthMatch A B (x,i)).2, fiberNthMatch_mem A B x hcard i i.property⟩
  invFun j := ⟨(fiberNthMatch B A (x,j)).2, fiberNthMatch_mem B A x hcard.symm j j.property⟩
  left_inv i := by
    apply Subtype.ext
    exact congrArg Prod.snd (fiberNthMatch_inverse A B x hcard i i.property)
  right_inv j := by
    apply Subtype.ext
    exact congrArg Prod.snd (fiberNthMatch_inverse B A x hcard.symm j j.property)

end
end MeasureUnitary

end Source46

/- Preserved source skeleton: FiberMultiplicityTransport -/
section Source47
/-! Equal multiplicities give an actual measure-preserving fiber
transport and hence a genuine base-module unitary. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace MeasureUnitary

open MeasureEquivalenceEquidecomposition

noncomputable section

local instance _root_.MeasureUnitary.instDecidable_fiberMultiplicityTransport (p : Prop) : Decidable p := Classical.propDecidable p

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem fiberRestrictedMeasure_apply (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (s : Set (X × ℕ)) (hs : MeasurableSet s) :
    fiberRestrictedMeasure μ A s =
      ∫⁻ x, ∑' i : ℕ, if x ∈ A i ∧ (x,i) ∈ s then (1 : ℝ≥0∞) else 0 ∂μ := by
  classical
  have hFA := measureFiberSet_measurable A hA
  calc
    fiberRestrictedMeasure μ A s = fiberAmbientMeasure μ (s ∩ measureFiberSet A) :=
      Measure.restrict_apply hs
    _ = ∫⁻ p, (s ∩ measureFiberSet A).indicator (fun _ => (1 : ℝ≥0∞)) p ∂fiberAmbientMeasure μ := by
      simp only [lintegral_indicator (hs.inter hFA), lintegral_one, Measure.restrict_apply_univ]
    _ = ∫⁻ x, ∫⁻ i : ℕ, (s ∩ measureFiberSet A).indicator (fun _ => (1 : ℝ≥0∞)) (x,i)
        ∂Measure.count ∂μ :=
      lintegral_prod _ (measurable_const.indicator (hs.inter hFA)).aemeasurable
    _ = _ := by
      congr 1
      funext x
      rw [lintegral_count]
      apply tsum_congr
      intro i
      by_cases ha : x ∈ A i <;> by_cases hsi : (x,i) ∈ s <;>
        simp [measureFiberSet,ha,hsi]

theorem fiberNthMatch_preserving (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B) :
    MeasurePreserving (fiberNthMatch A B) (fiberRestrictedMeasure μ A) (fiberRestrictedMeasure μ B) := by
  classical
  refine ⟨fiberNthMatch_measurable A B hA hB, ?_⟩
  ext s hs
  rw [Measure.map_apply (fiberNthMatch_measurable A B hA hB) hs,
    fiberRestrictedMeasure_apply μ A hA _ ((fiberNthMatch_measurable A B hA hB) hs),
    fiberRestrictedMeasure_apply μ B hB s hs]
  apply lintegral_congr_ae
  filter_upwards [hcard] with x hx
  let E := fiberActiveEquiv A B x hx
  change (∑' i : ℕ, if x ∈ A i ∧ fiberNthMatch A B (x,i) ∈ s then (1 : ℝ≥0∞) else 0) =
    ∑' j : ℕ, if x ∈ B j ∧ (x,j) ∈ s then (1 : ℝ≥0∞) else 0
  calc
    (∑' i : ℕ, if x ∈ A i ∧ fiberNthMatch A B (x,i) ∈ s then (1 : ℝ≥0∞) else 0) =
        ∑' i : {i : ℕ | x ∈ A i}, if fiberNthMatch A B (x,i.val) ∈ s then (1 : ℝ≥0∞) else 0 := by
      rw [tsum_subtype {i : ℕ | x ∈ A i}
        (fun i : ℕ => if fiberNthMatch A B (x,i) ∈ s then (1 : ℝ≥0∞) else 0)]
      apply tsum_congr
      intro i
      by_cases hi : x ∈ A i <;> simp [hi]
    _ = ∑' j : {j : ℕ | x ∈ B j}, if (x,j.val) ∈ s then (1 : ℝ≥0∞) else 0 :=
      E.tsum_eq (fun j : {j : ℕ | x ∈ B j} => if (x,j.val) ∈ s then (1 : ℝ≥0∞) else 0)
    _ = ∑' j : ℕ, if x ∈ B j ∧ (x,j) ∈ s then (1 : ℝ≥0∞) else 0 := by
      rw [tsum_subtype {j : ℕ | x ∈ B j}
        (fun j : ℕ => if (x,j) ∈ s then (1 : ℝ≥0∞) else 0)]
      apply tsum_congr
      intro j
      by_cases hj : x ∈ B j <;> simp [hj]

theorem fiberNthMatch_inverse_ae (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B) :
    ∀ᵐ p ∂fiberRestrictedMeasure μ A, fiberNthMatch B A (fiberNthMatch A B p) = p := by
  have hbase := (Measure.quasiMeasurePreserving_fst
    (μ := μ) (ν := (Measure.count : Measure ℕ))).ae hcard
  filter_upwards [ae_restrict_of_ae hbase, ae_restrict_mem (measureFiberSet_measurable A hA)]
    with p hp hA'
  exact fiberNthMatch_inverse A B p.1 hp p.2 hA'

def fiberMultiplicityUnitary (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B) :
    Lp ℂ 2 (fiberRestrictedMeasure μ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ B) :=
  pullbackUnitary (fiberRestrictedMeasure μ B) (fiberRestrictedMeasure μ A)
    (fiberNthMatch B A) (fiberNthMatch A B)
    (fiberNthMatch_preserving μ B A hB hA hcard.symm)
    (fiberNthMatch_preserving μ A B hA hB hcard)
    (fiberNthMatch_inverse_ae μ B A hB hcard.symm)

theorem fiberMultiplicityUnitary_coe (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B)
    (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    fiberMultiplicityUnitary μ A B hA hB hcard f =ᵐ[fiberRestrictedMeasure μ B]
      fun p => f (fiberNthMatch B A p) :=
  Lp.coeFn_compMeasurePreserving f (fiberNthMatch_preserving μ B A hB hA hcard.symm)



end
end MeasureUnitary

end Source47

/- Preserved source skeleton: FiberMeasureClass -/
section Source48
/-! Absolute continuity of a counting-fiber measure is exactly coordinatewise
absolute continuity of its restricted base measures. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 1500000

namespace MeasureUnitary

noncomputable section

local instance _root_.MeasureUnitary.instDecidable_fiberMeasureClass (p : Prop) : Decidable p := Classical.propDecidable p

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem fiberRestrictedMeasure_apply_sum (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (s : Set (X × ℕ)) (hs : MeasurableSet s) :
    fiberRestrictedMeasure μ A s = ∑' i : ℕ, μ.restrict (A i) ((fun x => (x,i)) ⁻¹' s) := by
  rw [fiberRestrictedMeasure_apply μ A hA s hs]
  have hmeas (i : ℕ) : Measurable (fun x => if x ∈ A i ∧ (x,i) ∈ s then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite ((hA i).inter (hs.preimage (measurable_id.prodMk measurable_const)))
      measurable_const measurable_const
  rw [lintegral_tsum (fun i => (hmeas i).aemeasurable)]
  apply tsum_congr
  intro i
  have heq : (fun x => if x ∈ A i ∧ (x,i) ∈ s then (1 : ℝ≥0∞) else 0) =
      (((fun x => (x,i)) ⁻¹' s) ∩ A i).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases ha : x ∈ A i <;> by_cases hsi : (x,i) ∈ s <;> simp [ha,hsi]
  have hslice : MeasurableSet ((fun x : X => (x,i)) ⁻¹' s) :=
    hs.preimage (measurable_id.prodMk (measurable_const (a := i)))
  rw [heq]
  exact (lintegral_indicator (hslice.inter (hA i)) (fun _ => (1 : ℝ≥0∞))).trans
    (by rw [lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hslice])

theorem fiberRestrictedMeasure_rectangle (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (s : Set X) (hs : MeasurableSet s) (i : ℕ) :
    fiberRestrictedMeasure μ A (s ×ˢ {i}) = μ.restrict (A i) s := by
  rw [Measure.restrict_apply (hs.prod (measurableSet_singleton i)), Measure.restrict_apply hs]
  have hset : (s ×ˢ {i}) ∩ measureFiberSet A = (s ∩ A i) ×ˢ {i} := by
    ext p
    rcases p with ⟨x,j⟩
    simp only [mem_inter_iff, mem_prod, mem_singleton_iff, measureFiberSet, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hx,hj⟩,ha⟩
      subst j
      exact ⟨⟨hx,ha⟩,rfl⟩
    · rintro ⟨⟨hx,ha⟩,hj⟩
      subst j
      exact ⟨⟨hx,rfl⟩,ha⟩
  rw [hset, Measure.prod_prod]
  simp only [Measure.count_singleton, mul_one]

variable (ν : Measure X) [IsFiniteMeasure ν]

theorem fiberRestrictedMeasure_absolutelyContinuous_iff (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    fiberRestrictedMeasure μ A ≪ fiberRestrictedMeasure ν B ↔
      ∀ i, μ.restrict (A i) ≪ ν.restrict (B i) := by
  constructor
  · intro h i
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hs0
    have hzero : fiberRestrictedMeasure ν B (s ×ˢ {i}) = 0 := by
      rw [fiberRestrictedMeasure_rectangle ν B hB s hs i, hs0]
    have hzero' := h hzero
    rwa [fiberRestrictedMeasure_rectangle μ A hA s hs i] at hzero'
  · intro h
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hs0
    rw [fiberRestrictedMeasure_apply_sum ν B hB s hs, ENNReal.tsum_eq_zero] at hs0
    rw [fiberRestrictedMeasure_apply_sum μ A hA s hs, ENNReal.tsum_eq_zero]
    intro i
    exact h i (hs0 i)

theorem fiberRestrictedMeasure_measureClass_iff (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    (fiberRestrictedMeasure μ A ≪ fiberRestrictedMeasure ν B ∧
      fiberRestrictedMeasure ν B ≪ fiberRestrictedMeasure μ A) ↔
      ∀ i, μ.restrict (A i) ≪ ν.restrict (B i) ∧ ν.restrict (B i) ≪ μ.restrict (A i) := by
  rw [fiberRestrictedMeasure_absolutelyContinuous_iff μ ν A B hA hB,
    fiberRestrictedMeasure_absolutelyContinuous_iff ν μ B A hB hA]
  exact forall_and.symm

end
end MeasureUnitary

end Source48

/- Preserved source skeleton: FiberMultiplicityClassification -/
section Source49
/-! Complete same-base spectral multiplicity classification on counting fibers. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]



theorem fiberMultiplicityUnitary_intertwines_phase (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hcard : fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B)
    (c : X → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)
    (f : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    fiberMultiplicityUnitary μ A B hA hB hcard
      (phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) f) =
      phaseEquiv (fiberRestrictedMeasure μ B) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberMultiplicityUnitary μ A B hA hB hcard f) := by
  apply Lp.ext
  filter_upwards [fiberMultiplicityUnitary_coe μ A B hA hB hcard
      (phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) f),
    (fiberNthMatch_preserving μ B A hB hA hcard.symm).quasiMeasurePreserving.ae
      (phaseMap_coe (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) f),
    phaseMap_coe (fiberRestrictedMeasure μ B) (fun p => c p.1) (hc.comp measurable_fst)
      (fun p => hnorm p.1) (fiberMultiplicityUnitary μ A B hA hB hcard f),
    fiberMultiplicityUnitary_coe μ A B hA hB hcard f] with p hleft hin hright hf
  change ((phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
    (fun p => hnorm p.1)) f) (fiberNthMatch B A p) = _ at hin
  change ((phaseEquiv (fiberRestrictedMeasure μ B) (fun p => c p.1) (hc.comp measurable_fst)
    (fun p => hnorm p.1)) (fiberMultiplicityUnitary μ A B hA hB hcard f)) p = _ at hright
  rw [hleft, hin, hright, hf]
  rfl

open OperatorCoding

variable (ρ : Measure SpectralCircle) [IsFiniteMeasure ρ]

def fiberCoordinateUnitary (A : ℕ → Set SpectralCircle) :
    Lp ℂ 2 (fiberRestrictedMeasure ρ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure ρ A) :=
  phaseEquiv (fiberRestrictedMeasure ρ A) (fun p => circleCoordinate p.1)
    (circleCoordinate.continuous.measurable.comp measurable_fst)
    (fun p => circleCoordinate_norm p.1)

theorem fiberCoordinateUnitary_intertwiner_projections
    (A B : ℕ → Set SpectralCircle)
    (U : Lp ℂ 2 (fiberRestrictedMeasure ρ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure ρ B))
    (hU : ∀ f, U (fiberCoordinateUnitary ρ A f) = fiberCoordinateUnitary ρ B (U f)) :
    ∀ (s : Set SpectralCircle) (hs : MeasurableSet s) (f : Lp ℂ 2 (fiberRestrictedMeasure ρ A)),
      U (indicatorL2 (fiberRestrictedMeasure ρ A) (hs.preimage measurable_fst) f) =
        indicatorL2 (fiberRestrictedMeasure ρ B) (hs.preimage measurable_fst) (U f) := by
  apply projections_intertwine_of_continuous_multipliers
    (fiberRestrictedMeasure ρ A) (fiberRestrictedMeasure ρ B)
    Prod.fst Prod.fst measurable_fst measurable_fst U
  apply continuous_intertwines_of_separating_phases
    (fiberRestrictedMeasure ρ A) (fiberRestrictedMeasure ρ B)
    Prod.fst Prod.fst measurable_fst measurable_fst
    (fun _ : Unit => circleCoordinate) (fun _ => circleCoordinate_norm)
  · intro x y hxy
    exact ⟨(), fun h => hxy (Subtype.ext h)⟩
  · intro i f
    exact hU f

theorem fiberCoordinateUnitary_classification (A B : ℕ → Set SpectralCircle)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    (∃ U : Lp ℂ 2 (fiberRestrictedMeasure ρ A) ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure ρ B),
      ∀ f, U (fiberCoordinateUnitary ρ A f) = fiberCoordinateUnitary ρ B (U f)) ↔
      fiberMultiplicity A =ᵐ[ρ] fiberMultiplicity B := by
  constructor
  · rintro ⟨U,hU⟩
    exact fiberMultiplicity_eq_of_intertwiner ρ A B hA hB U
      (fiberCoordinateUnitary_intertwiner_projections ρ A B U hU)
  · intro hcard
    exact ⟨fiberMultiplicityUnitary ρ A B hA hB hcard,
      fiberMultiplicityUnitary_intertwines_phase ρ A B hA hB hcard circleCoordinate
        circleCoordinate.continuous.measurable circleCoordinate_norm⟩

end
end MeasureUnitary

end Source49

/- Preserved source skeleton: FiberMultiplicityLayers -/
section Source50
/-! Canonical multiplicity layers recover the finite-or-countable rank. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X]

def multiplicityLayer (A : ℕ → Set X) (n : ℕ) : Set X :=
  {x | (n : ℝ≥0∞) < fiberMultiplicity A x}

theorem multiplicityLayer_measurable (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    MeasurableSet (multiplicityLayer A n) :=
  measurableSet_lt measurable_const (fiberMultiplicity_measurable A hA)

theorem enat_eq_of_natCuts (a b : ℕ∞)
    (h : ∀ n : ℕ, (n : ℕ∞) < a ↔ (n : ℕ∞) < b) : a = b := by
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe n => exact False.elim ((lt_irrefl (n : ℕ∞)) ((h n).mp (ENat.coe_lt_top n)))
  | coe m =>
    induction b using ENat.recTopCoe with
    | top => exact False.elim ((lt_irrefl (m : ℕ∞)) ((h m).mpr (ENat.coe_lt_top m)))
    | coe n =>
      congr 1
      apply le_antisymm
      · by_contra hmn
        have hlt : (n : ℕ∞) < (m : ℕ∞) := ENat.coe_lt_coe.mpr (lt_of_not_ge hmn)
        exact (lt_irrefl (n : ℕ∞)) ((h n).mp hlt)
      · by_contra hnm
        have hlt : (m : ℕ∞) < (n : ℕ∞) := ENat.coe_lt_coe.mpr (lt_of_not_ge hnm)
        exact (lt_irrefl (m : ℕ∞)) ((h m).mpr hlt)

theorem fiberMultiplicity_eq_of_layers (A B : ℕ → Set X) (x : X)
    (h : ∀ n, x ∈ multiplicityLayer A n ↔ x ∈ multiplicityLayer B n) :
    fiberMultiplicity A x = fiberMultiplicity B x := by
  have hc : {i : ℕ | x ∈ A i}.encard = {i : ℕ | x ∈ B i}.encard := by
    apply enat_eq_of_natCuts
    intro n
    have hn := h n
    change (n : ℝ≥0∞) < fiberMultiplicity A x ↔ (n : ℝ≥0∞) < fiberMultiplicity B x at hn
    rw [fiberMultiplicity_eq_encard, fiberMultiplicity_eq_encard] at hn
    simpa only [← ENat.toENNReal_coe n, ENat.toENNReal_lt] using hn
  rw [fiberMultiplicity_eq_encard, fiberMultiplicity_eq_encard, hc]

theorem restrict_measureClass_iff_ae (μ : Measure X) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ.restrict s ≪ μ.restrict t ∧ μ.restrict t ≪ μ.restrict s) ↔ s =ᵐ[μ] t := by
  constructor
  · rintro ⟨hst,hts⟩
    have hst' := ae_imp_of_ae_restrict ((Measure.AbsolutelyContinuous.ae_le hst) (ae_restrict_mem ht))
    have hts' := ae_imp_of_ae_restrict ((Measure.AbsolutelyContinuous.ae_le hts) (ae_restrict_mem hs))
    filter_upwards [hst',hts'] with x hx hy
    exact propext ⟨hx,hy⟩
  · intro hst
    have heq : μ.restrict s = μ.restrict t := Measure.restrict_congr_set hst
    rw [heq]
    exact ⟨Measure.AbsolutelyContinuous.rfl,Measure.AbsolutelyContinuous.rfl⟩

theorem multiplicityLayer_measureClass_iff (μ : Measure X) (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    (∀ n, μ.restrict (multiplicityLayer A n) ≪ μ.restrict (multiplicityLayer B n) ∧
      μ.restrict (multiplicityLayer B n) ≪ μ.restrict (multiplicityLayer A n)) ↔
        fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B := by
  constructor
  · intro h
    have hcuts (n : ℕ) : multiplicityLayer A n =ᵐ[μ] multiplicityLayer B n :=
      (restrict_measureClass_iff_ae μ _ _ (multiplicityLayer_measurable A hA n)
        (multiplicityLayer_measurable B hB n)).mp (h n)
    filter_upwards [ae_all_iff.mpr hcuts] with x hx
    exact fiberMultiplicity_eq_of_layers A B x (fun n => (hx n).to_iff)
  · intro h n
    apply (restrict_measureClass_iff_ae μ _ _ (multiplicityLayer_measurable A hA n)
      (multiplicityLayer_measurable B hB n)).mpr
    filter_upwards [h] with x hx
    change ((n : ℝ≥0∞) < fiberMultiplicity A x) = ((n : ℝ≥0∞) < fiberMultiplicity B x)
    rw [hx]

end
end MeasureUnitary

end Source50

/- Preserved source skeleton: FiberMultiplicityMeasureCode -/
section Source51
/-! Positive finite counting weights give a finite measure-class code for
all multiplicity layers, without changing any of their null sets. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X]

def weightedFiberMeasure (μ : Measure X) (A : ℕ → Set X) (w : Measure ℕ) : Measure (X × ℕ) :=
  (μ.prod w).restrict (measureFiberSet A)

instance weightedFiberMeasure_finite (μ : Measure X) [IsFiniteMeasure μ]
    (A : ℕ → Set X) (w : Measure ℕ) [IsFiniteMeasure w] :
    IsFiniteMeasure (weightedFiberMeasure μ A w) := by
  unfold weightedFiberMeasure
  infer_instance

theorem count_measureClass_of_singletons (w : Measure ℕ) (hw : ∀ i, w {i} ≠ 0) :
    (Measure.count : Measure ℕ) ≪ w ∧ w ≪ (Measure.count : Measure ℕ) := by
  constructor
  · intro s hs
    apply Measure.count_eq_zero_iff.mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hw i (measure_mono_null (Set.singleton_subset_iff.mpr hi) hs)
  · intro s hs
    rw [Measure.count_eq_zero_iff.mp hs]
    exact measure_empty

theorem weightedFiberMeasure_measureClass_count (μ : Measure X) [IsFiniteMeasure μ]
    (A : ℕ → Set X) (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ i, w {i} ≠ 0) :
    fiberRestrictedMeasure μ A ≪ weightedFiberMeasure μ A w ∧
      weightedFiberMeasure μ A w ≪ fiberRestrictedMeasure μ A := by
  have h := count_measureClass_of_singletons w hw
  exact ⟨((Measure.AbsolutelyContinuous.rfl (μ := μ)).prod h.1).restrict _,
    ((Measure.AbsolutelyContinuous.rfl (μ := μ)).prod h.2).restrict _⟩

theorem weightedFiberMeasure_measureClass_iff (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A B : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (w w' : Measure ℕ) [IsFiniteMeasure w] [IsFiniteMeasure w']
    (hw : ∀ i, w {i} ≠ 0) (hw' : ∀ i, w' {i} ≠ 0) :
    (weightedFiberMeasure μ A w ≪ weightedFiberMeasure ν B w' ∧
      weightedFiberMeasure ν B w' ≪ weightedFiberMeasure μ A w) ↔
      ∀ i, μ.restrict (A i) ≪ ν.restrict (B i) ∧ ν.restrict (B i) ≪ μ.restrict (A i) := by
  have hμ := weightedFiberMeasure_measureClass_count μ A w hw
  have hν := weightedFiberMeasure_measureClass_count ν B w' hw'
  rw [← fiberRestrictedMeasure_measureClass_iff μ ν A B hA hB]
  constructor
  · rintro ⟨hAB,hBA⟩
    exact ⟨hμ.1.trans (hAB.trans hν.2),hν.1.trans (hBA.trans hμ.2)⟩
  · rintro ⟨hAB,hBA⟩
    exact ⟨hμ.2.trans (hAB.trans hν.1),hν.2.trans (hBA.trans hμ.1)⟩

def multiplicityLayerCode (μ : Measure X) (A : ℕ → Set X) (w : Measure ℕ) : Measure (X × ℕ) :=
  weightedFiberMeasure μ (multiplicityLayer A) w

instance multiplicityLayerCode_finite (μ : Measure X) [IsFiniteMeasure μ]
    (A : ℕ → Set X) (w : Measure ℕ) [IsFiniteMeasure w] :
    IsFiniteMeasure (multiplicityLayerCode μ A w) := by
  unfold multiplicityLayerCode
  infer_instance

theorem multiplicityLayerCode_classification (μ : Measure X) [IsFiniteMeasure μ]
    (A B : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ i, w {i} ≠ 0) :
    (multiplicityLayerCode μ A w ≪ multiplicityLayerCode μ B w ∧
      multiplicityLayerCode μ B w ≪ multiplicityLayerCode μ A w) ↔
      fiberMultiplicity A =ᵐ[μ] fiberMultiplicity B := by
  rw [multiplicityLayerCode, multiplicityLayerCode,
    weightedFiberMeasure_measureClass_iff μ μ (multiplicityLayer A) (multiplicityLayer B)
      (multiplicityLayer_measurable A hA) (multiplicityLayer_measurable B hB) w w hw hw]
  exact multiplicityLayer_measureClass_iff μ A B hA hB

end
end MeasureUnitary

end Source51

/- Preserved source skeleton: FiberMultiplicityBaseChange -/
section Source52
/-! Changing a dominating base restricts every support to its actual
Radon–Nikodym support; the multiplicity-layer code retains its measure class. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

local instance _root_.MeasureUnitary.instDecidable_fiberMultiplicityBaseChange (p : Prop) : Decidable p := Classical.propDecidable p

variable {X : Type*} [MeasurableSpace X]

def rnSupport (μ ρ : Measure X) : Set X := {x | μ.rnDeriv ρ x ≠ 0}

theorem rnSupport_measurable (μ ρ : Measure X) : MeasurableSet (rnSupport μ ρ) :=
  (measurableSet_eq_fun (Measure.measurable_rnDeriv μ ρ) measurable_const).compl

theorem rnSupport_measureClass (μ ρ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (hμρ : μ ≪ ρ) : μ ≪ ρ.restrict (rnSupport μ ρ) ∧ ρ.restrict (rnSupport μ ρ) ≪ μ := by
  have heq : ae (ρ.withDensity (μ.rnDeriv ρ)) = ae (ρ.restrict (rnSupport μ ρ)) := by
    ext s
    exact ae_withDensity_iff_ae_restrict (Measure.measurable_rnDeriv μ ρ)
  rw [Measure.withDensity_rnDeriv_eq μ ρ hμρ] at heq
  exact ⟨Measure.ae_le_iff_absolutelyContinuous.mp heq.le,
    Measure.ae_le_iff_absolutelyContinuous.mp heq.symm.le⟩

def supportedFamily (A : ℕ → Set X) (C : Set X) (i : ℕ) : Set X := A i ∩ C

theorem supportedFamily_measurable (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (C : Set X) (hC : MeasurableSet C) (i : ℕ) : MeasurableSet (supportedFamily A C i) :=
  (hA i).inter hC

theorem fiberMultiplicity_supportedFamily (A : ℕ → Set X) (C : Set X) (x : X) :
    fiberMultiplicity (supportedFamily A C) x =
      if x ∈ C then fiberMultiplicity A x else 0 := by
  classical
  by_cases hx : x ∈ C <;> simp [fiberMultiplicity,supportedFamily,Set.indicator_apply,hx]

theorem multiplicityLayer_supportedFamily (A : ℕ → Set X) (C : Set X) (n : ℕ) :
    multiplicityLayer (supportedFamily A C) n = multiplicityLayer A n ∩ C := by
  classical
  ext x
  change ((n : ℝ≥0∞) < fiberMultiplicity (supportedFamily A C) x) ↔
    (n : ℝ≥0∞) < fiberMultiplicity A x ∧ x ∈ C
  rw [fiberMultiplicity_supportedFamily]
  by_cases hx : x ∈ C <;> simp [hx]

theorem restrict_measureClass_baseChange (μ ρ : Measure X) (C s : Set X)
    (hs : MeasurableSet s) (hμρ : μ ≪ ρ.restrict C) (hρμ : ρ.restrict C ≪ μ) :
    μ.restrict s ≪ ρ.restrict (s ∩ C) ∧ ρ.restrict (s ∩ C) ≪ μ.restrict s := by
  have h1 := hμρ.restrict s
  have h2 := hρμ.restrict s
  rw [Measure.restrict_restrict hs] at h1 h2
  exact ⟨h1,h2⟩

theorem multiplicityLayerCode_baseChange (μ ρ : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ρ] (A : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (C : Set X) (hC : MeasurableSet C)
    (hμρ : μ ≪ ρ.restrict C) (hρμ : ρ.restrict C ≪ μ)
    (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ i, w {i} ≠ 0) :
    multiplicityLayerCode μ A w ≪ multiplicityLayerCode ρ (supportedFamily A C) w ∧
      multiplicityLayerCode ρ (supportedFamily A C) w ≪ multiplicityLayerCode μ A w := by
  apply (weightedFiberMeasure_measureClass_iff μ ρ (multiplicityLayer A)
    (multiplicityLayer (supportedFamily A C)) (multiplicityLayer_measurable A hA)
    (multiplicityLayer_measurable (supportedFamily A C) (supportedFamily_measurable A hA C hC))
      w w hw hw).mpr
  intro n
  rw [multiplicityLayer_supportedFamily]
  exact restrict_measureClass_baseChange μ ρ C (multiplicityLayer A n)
    (multiplicityLayer_measurable A hA n) hμρ hρμ

end
end MeasureUnitary

end Source52

/- Preserved source skeleton: FiberL2HilbertSum -/
section Source53
/-! Actual identification of the Hilbert sum of L²(μ|A_i) with the L²
space of the corresponding measurable counting fibers. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 2000000

namespace MeasureUnitary

open MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Restriction

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem fiberInjection_supported (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (f : Lp ℂ 2 (μ.restrict (A i))) :
    indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA)
      (injection μ i (zeroExtend μ (A i) (hA i) f)) =
        injection μ i (zeroExtend μ (A i) (hA i) f) := by
  rw [← fiber_injection_indicator μ A hA i]
  have hsupport : indicatorL2 μ (hA i) (zeroExtend μ (A i) (hA i) f) =
      zeroExtend μ (A i) (hA i) f := by
    rw [← zeroExtend_restrict μ (A i) (hA i), restrict_zeroExtend]
  rw [hsupport]

def fiberComponentInjection (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) (i : ℕ) :
    Lp ℂ 2 (μ.restrict (A i)) →ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ A) where
  toLinearMap := ((restrictCLM (fiberAmbientMeasure μ) (measureFiberSet A)).comp
    ((injectionLI μ i).toContinuousLinearMap.comp
      (zeroExtendLI μ (A i) (hA i)).toContinuousLinearMap)).toLinearMap
  norm_map' f := by
    change ‖restrictMap (fiberAmbientMeasure μ) (measureFiberSet A)
      (injection μ i (zeroExtend μ (A i) (hA i) f))‖ = ‖f‖
    rw [← zeroExtend_norm (fiberAmbientMeasure μ) (measureFiberSet A)
      (measureFiberSet_measurable A hA), zeroExtend_restrict,
      fiberInjection_supported μ A hA i f, injection_norm, zeroExtend_norm]

theorem fiberComponentInjection_zeroExtend (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (f : Lp ℂ 2 (μ.restrict (A i))) :
    zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
      (fiberComponentInjection μ A hA i f) = injection μ i (zeroExtend μ (A i) (hA i) f) := by
  change zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
    (restrictMap (fiberAmbientMeasure μ) (measureFiberSet A)
      (injection μ i (zeroExtend μ (A i) (hA i) f))) = _
  rw [zeroExtend_restrict, fiberInjection_supported μ A hA i f]

theorem fiberComponentInjection_inner (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (f : Lp ℂ 2 (μ.restrict (A i))) (g : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    inner ℂ (fiberComponentInjection μ A hA i f) g =
      inner ℂ f (restrictMap μ (A i)
        (coefficient μ i (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
          (measureFiberSet_measurable A hA) g))) := by
  rw [← (zeroExtendLI (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA)).inner_map_map,
    ]
  change inner ℂ (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
    (fiberComponentInjection μ A hA i f)) (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA) g) = _
  rw [fiberComponentInjection_zeroExtend, inner_injection_coefficient, inner_zeroExtend_restrict]

theorem fiberComponents_orthogonal (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    OrthogonalFamily ℂ (fun i => Lp ℂ 2 (μ.restrict (A i))) (fiberComponentInjection μ A hA) := by
  intro i j hij f g
  rw [← (zeroExtendLI (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA)).inner_map_map,
    ]
  change inner ℂ (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
    (fiberComponentInjection μ A hA i f)) (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA) (fiberComponentInjection μ A hA j g)) = 0
  rw [fiberComponentInjection_zeroExtend, fiberComponentInjection_zeroExtend,
    inner_injection_coefficient, coefficient_injection, if_neg hij, inner_zero_right]

theorem fiberCoefficient_supported (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (g : Lp ℂ 2 (fiberRestrictedMeasure μ A)) :
    indicatorL2 μ (hA i) (coefficient μ i
      (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g)) =
    coefficient μ i
      (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g) := by
  have hsupport : indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA)
      (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g) =
      zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g := by
    rw [← zeroExtend_restrict (fiberAmbientMeasure μ) (measureFiberSet A)
      (measureFiberSet_measurable A hA), restrict_zeroExtend]
  have h := coefficient_indicator μ id measurable_id (measureFiberSet A)
    (measureFiberSet_measurable A hA) i
    (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g)
  change coefficient μ i (indicatorL2 (fiberAmbientMeasure μ) (measureFiberSet_measurable A hA)
    (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g)) = _ at h
  rw [hsupport] at h
  exact h.symm

theorem fiberComponents_total (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    ⊤ ≤ (⨆ i : ℕ, (fiberComponentInjection μ A hA i).toLinearMap.range).topologicalClosure := by
  let S := (⨆ i : ℕ, (fiberComponentInjection μ A hA i).toLinearMap.range).topologicalClosure
  letI : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe
  have hbot : Sᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    have hcoeff (i : ℕ) : coefficient μ i
        (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g) = 0 := by
      let z := restrictMap μ (A i) (coefficient μ i
        (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA) g))
      have hz : z = 0 := by
        have hmem : fiberComponentInjection μ A hA i z ∈ S :=
          Submodule.le_topologicalClosure _ (le_iSup
            (fun j => (fiberComponentInjection μ A hA j).toLinearMap.range) i ⟨z,rfl⟩)
        have hip := hg _ hmem
        rw [fiberComponentInjection_inner] at hip
        exact inner_self_eq_zero.mp hip
      calc
        coefficient μ i (zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
            (measureFiberSet_measurable A hA) g) = zeroExtend μ (A i) (hA i) z := by
          rw [zeroExtend_restrict, fiberCoefficient_supported μ A hA i g]
        _ = 0 := by
          rw [hz]
          exact (zeroExtendLI μ (A i) (hA i)).map_zero
    have hzero : zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A)
        (measureFiberSet_measurable A hA) g = 0 := by
      apply coefficient_ext μ
      intro i
      rw [hcoeff]
      exact ((coefficientCLM μ i).map_zero).symm
    have hn : ‖g‖ = 0 := by
      rw [← zeroExtend_norm (fiberAmbientMeasure μ) (measureFiberSet A)
        (measureFiberSet_measurable A hA), hzero, norm_zero]
    exact norm_eq_zero.mp hn
  exact le_of_eq (Submodule.orthogonal_eq_bot_iff.mp hbot).symm

def fiberL2HilbertSum (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    IsHilbertSum ℂ (fun i => Lp ℂ 2 (μ.restrict (A i))) (fiberComponentInjection μ A hA) :=
  IsHilbertSum.mk (fiberComponents_orthogonal μ A hA) (fiberComponents_total μ A hA)

def fiberL2SumEquiv (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    lp (fun i => Lp ℂ 2 (μ.restrict (A i))) 2 ≃ₗᵢ[ℂ] Lp ℂ 2 (fiberRestrictedMeasure μ A) :=
  (fiberL2HilbertSum μ A hA).linearIsometryEquiv.symm

end
end MeasureUnitary

end Source53

/- Preserved source skeleton: FiberL2SpectralSum -/
section Source54
/-! The Hilbert-sum/fiber identification respects the actual coordinate unitary. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace MeasureUnitary

open MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Restriction

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

 

theorem zeroExtend_phase (A : Set X) (hA : MeasurableSet A)
    (c : X → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)
    (f : Lp ℂ 2 (μ.restrict A)) :
    zeroExtend μ A hA (phaseEquiv (μ.restrict A) c hc hnorm f) =
      phaseEquiv μ c hc hnorm (zeroExtend μ A hA f) := by
  apply Lp.ext
  have hsource := (ae_eq_restrict_iff_indicator_ae_eq hA).mp
    (phaseMap_coe (μ.restrict A) c hc hnorm f)
  filter_upwards [zeroExtend_coe μ A hA (phaseEquiv (μ.restrict A) c hc hnorm f),
    hsource, phaseMap_coe μ c hc hnorm (zeroExtend μ A hA f),
    zeroExtend_coe μ A hA f] with x hleft hs hright hf
  change A.indicator ((phaseEquiv (μ.restrict A) c hc hnorm) f) x = _ at hs
  change ((phaseEquiv μ c hc hnorm) (zeroExtend μ A hA f)) x = _ at hright
  rw [hleft, hs, hright, hf]
  by_cases hx : x ∈ A <;> simp [hx]

variable [IsFiniteMeasure μ]

theorem injection_phase (i : ℕ) (c : X → ℂ) (hc : Measurable c)
    (hnorm : ∀ x, ‖c x‖ = 1) (f : Lp ℂ 2 μ) :
    injection μ i (phaseEquiv μ c hc hnorm f) =
      phaseEquiv (fiberAmbientMeasure μ) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (injection μ i f) := by
  apply Lp.ext
  filter_upwards [injection_coe μ i (phaseEquiv μ c hc hnorm f),
    phaseMap_coe (fiberAmbientMeasure μ) (fun p => c p.1) (hc.comp measurable_fst)
      (fun p => hnorm p.1) (injection μ i f), injection_coe μ i f,
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (Measure.count : Measure ℕ))).ae
      (phaseMap_coe μ c hc hnorm f)] with p hleft hright hinj hphase
  change ((phaseEquiv (fiberAmbientMeasure μ) (fun p => c p.1) (hc.comp measurable_fst)
    (fun p => hnorm p.1)) (injection μ i f)) p = _ at hright
  change ((phaseEquiv μ c hc hnorm) f) p.1 = _ at hphase
  rw [hleft, hright, hinj]
  by_cases hp : p.2 = i <;> simp [injectionFun,hp,hphase]

theorem fiberComponentInjection_phase (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (c : X → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)
    (f : Lp ℂ 2 (μ.restrict (A i))) :
    fiberComponentInjection μ A hA i (phaseEquiv (μ.restrict (A i)) c hc hnorm f) =
      phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberComponentInjection μ A hA i f) := by
  apply (zeroExtendLI (fiberAmbientMeasure μ) (measureFiberSet A)
    (measureFiberSet_measurable A hA)).injective
  change zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
    (fiberComponentInjection μ A hA i (phaseEquiv (μ.restrict (A i)) c hc hnorm f)) =
    zeroExtend (fiberAmbientMeasure μ) (measureFiberSet A) (measureFiberSet_measurable A hA)
      (phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberComponentInjection μ A hA i f))
  rw [fiberComponentInjection_zeroExtend, zeroExtend_phase, zeroExtend_phase,
    fiberComponentInjection_zeroExtend, injection_phase]

def fiberSumPhaseUnitary (A : ℕ → Set X) (c : X → ℂ) (hc : Measurable c)
    (hnorm : ∀ x, ‖c x‖ = 1) :
    lp (fun i => Lp ℂ 2 (μ.restrict (A i))) 2 ≃ₗᵢ[ℂ]
      lp (fun i => Lp ℂ 2 (μ.restrict (A i))) 2 :=
  hilbertFamilyCongr (fun i => phaseEquiv (μ.restrict (A i)) c hc hnorm)

theorem fiberL2SumEquiv_single (A : ℕ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (i : ℕ) (f : Lp ℂ 2 (μ.restrict (A i))) :
    fiberL2SumEquiv μ A hA (lp.single 2 i f) = fiberComponentInjection μ A hA i f :=
  (fiberL2HilbertSum μ A hA).linearIsometryEquiv_symm_apply_single f

theorem fiberL2SumEquiv_intertwines_phase (A : ℕ → Set X)
    (hA : ∀ i, MeasurableSet (A i)) (c : X → ℂ) (hc : Measurable c)
    (hnorm : ∀ x, ‖c x‖ = 1) (f : lp (fun i => Lp ℂ 2 (μ.restrict (A i))) 2) :
    fiberL2SumEquiv μ A hA (fiberSumPhaseUnitary μ A c hc hnorm f) =
      phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberL2SumEquiv μ A hA f) := by
  have hmaps : (fiberL2SumEquiv μ A hA).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fiberSumPhaseUnitary μ A c hc hnorm).toContinuousLinearEquiv.toContinuousLinearMap =
      (phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fiberL2SumEquiv μ A hA).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    intro i
    apply ContinuousLinearMap.ext
    intro g
    change fiberL2SumEquiv μ A hA
      (hilbertFamilyCongr (fun j => phaseEquiv (μ.restrict (A j)) c hc hnorm) (lp.single 2 i g)) =
      phaseEquiv (fiberRestrictedMeasure μ A) (fun p => c p.1) (hc.comp measurable_fst)
        (fun p => hnorm p.1) (fiberL2SumEquiv μ A hA (lp.single 2 i g))
    rw [hilbertFamilyCongr_single, fiberL2SumEquiv_single, fiberL2SumEquiv_single]
    exact fiberComponentInjection_phase μ A hA i c hc hnorm g
  exact congrArg (fun T => T f) hmaps

end
end MeasureUnitary

end Source54

/- Preserved source skeleton: UnitaryDominatedSpectralModel -/
section Source55
/-! The genuine fiber model for a countable cyclic spectral decomposition
with a finite dominating measure. The supplied absolute-continuity facts
are precisely the Radon–Nikodym support identities, not a classification
assumption. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]
    (U : StrongUnitary H) (ρ : Measure SpectralCircle) [IsFiniteMeasure ρ]
    (A : ℕ → Set SpectralCircle)
    (hμρ : ∀ n, greedySpectralMeasure U n ≪ ρ.restrict (A n))
    (hρμ : ∀ n, ρ.restrict (A n) ≪ greedySpectralMeasure U n)

def unitaryDominatedSumEquiv :
    lp (fun n => Lp ℂ 2 (ρ.restrict (A n))) 2 ≃ₗᵢ[ℂ] UnitarySpectralSum U :=
  hilbertFamilyCongr (fun n => rnWeightedEquiv (ρ.restrict (A n))
    (greedySpectralMeasure U n) (hρμ n) (hμρ n))

theorem unitaryDominatedSumEquiv_intertwines
    (f : lp (fun n => Lp ℂ 2 (ρ.restrict (A n))) 2) :
    unitaryDominatedSumEquiv U ρ A hμρ hρμ
      (fiberSumPhaseUnitary ρ A circleCoordinate circleCoordinate.continuous.measurable
        circleCoordinate_norm f) =
      spectralSumUnitary U (unitaryDominatedSumEquiv U ρ A hμρ hρμ f) := by
  apply lp.ext
  funext n
  change rnWeightedEquiv (ρ.restrict (A n)) (greedySpectralMeasure U n) (hρμ n) (hμρ n)
      (phaseEquiv (ρ.restrict (A n)) circleCoordinate circleCoordinate.continuous.measurable
        circleCoordinate_norm (f n)) =
    phaseEquiv (greedySpectralMeasure U n) circleCoordinate circleCoordinate.continuous.measurable
      circleCoordinate_norm (rnWeightedEquiv (ρ.restrict (A n))
        (greedySpectralMeasure U n) (hρμ n) (hμρ n) (f n))
  exact rnWeightedEquiv_intertwines_phase (ρ.restrict (A n)) circleCoordinate
    circleCoordinate.continuous.measurable circleCoordinate_norm (greedySpectralMeasure U n)
      (hρμ n) (hμρ n) (f n)

def unitaryDominatedFiberEquiv (hA : ∀ n, MeasurableSet (A n)) :
    Lp ℂ 2 (fiberRestrictedMeasure ρ A) ≃ₗᵢ[ℂ] H :=
  ((fiberL2SumEquiv ρ A hA).symm.trans (unitaryDominatedSumEquiv U ρ A hμρ hρμ)).trans
    (unitarySpectralSumEquiv U)

theorem unitaryDominatedFiberEquiv_intertwines (hA : ∀ n, MeasurableSet (A n))
    (f : Lp ℂ 2 (fiberRestrictedMeasure ρ A)) :
    unitaryDominatedFiberEquiv U ρ A hμρ hρμ hA (fiberCoordinateUnitary ρ A f) =
      U (unitaryDominatedFiberEquiv U ρ A hμρ hρμ hA f) := by
  have hf : (fiberL2SumEquiv ρ A hA).symm (fiberCoordinateUnitary ρ A f) =
      fiberSumPhaseUnitary ρ A circleCoordinate circleCoordinate.continuous.measurable
        circleCoordinate_norm ((fiberL2SumEquiv ρ A hA).symm f) := by
    apply (fiberL2SumEquiv ρ A hA).injective
    rw [LinearIsometryEquiv.apply_symm_apply, fiberL2SumEquiv_intertwines_phase,
      LinearIsometryEquiv.apply_symm_apply]
    rfl
  change unitarySpectralSumEquiv U (unitaryDominatedSumEquiv U ρ A hμρ hρμ
    ((fiberL2SumEquiv ρ A hA).symm (fiberCoordinateUnitary ρ A f))) = _
  rw [hf, unitaryDominatedSumEquiv_intertwines, unitarySpectralSumEquiv_intertwines]
  rfl

variable (V : StrongUnitary H) (B : ℕ → Set SpectralCircle)
    (hνρ : ∀ n, greedySpectralMeasure V n ≪ ρ.restrict (B n))
    (hρν : ∀ n, ρ.restrict (B n) ≪ greedySpectralMeasure V n)

include hμρ hρμ hνρ hρν in
theorem unitaryDominatedFiber_classification
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n)) :
    (∃ W : H ≃ₗᵢ[ℂ] H, ∀ x, W (U x) = V (W x)) ↔
      fiberMultiplicity A =ᵐ[ρ] fiberMultiplicity B := by
  let FA := unitaryDominatedFiberEquiv U ρ A hμρ hρμ hA
  let FB := unitaryDominatedFiberEquiv V ρ B hνρ hρν hB
  have hFA (f : Lp ℂ 2 (fiberRestrictedMeasure ρ A)) :
      FA (fiberCoordinateUnitary ρ A f) = U (FA f) :=
    unitaryDominatedFiberEquiv_intertwines U ρ A hμρ hρμ hA f
  have hFB (f : Lp ℂ 2 (fiberRestrictedMeasure ρ B)) :
      FB (fiberCoordinateUnitary ρ B f) = V (FB f) :=
    unitaryDominatedFiberEquiv_intertwines V ρ B hνρ hρν hB f
  rw [← fiberCoordinateUnitary_classification ρ A B hA hB]
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨(FA.trans W).trans FB.symm, ?_⟩
    intro f
    apply FB.injective
    change FB (FB.symm (W (FA (fiberCoordinateUnitary ρ A f)))) =
      FB (fiberCoordinateUnitary ρ B (FB.symm (W (FA f))))
    rw [LinearIsometryEquiv.apply_symm_apply, hFA, hW, hFB,
      LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨C,hC⟩
    refine ⟨(FA.symm.trans C).trans FB, ?_⟩
    intro x
    have hi : FA.symm (U x) = fiberCoordinateUnitary ρ A (FA.symm x) := by
      apply FA.injective
      rw [LinearIsometryEquiv.apply_symm_apply, hFA, LinearIsometryEquiv.apply_symm_apply]
    change FB (C (FA.symm (U x))) = V (FB (C (FA.symm x)))
    rw [hi,hC,hFB]

end
end OperatorCoding

end Source55

/- Preserved source skeleton: UnitarySpectralMeasureClassification -/
section Source56
/-! The complete measure-class invariant of an arbitrary unitary from its
actual countable cyclic decomposition, for any finite dominating support
presentation. The comparison uses the genuine common base μ+ν and its
Radon–Nikodym supports. -/

open MeasureTheory Set Filter
open scoped ENNReal

set_option maxHeartbeats 2000000

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

 theorem unitary_multiplicityLayerCode_classification
    (U V : StrongUnitary H) (μ ν : Measure SpectralCircle)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A B : ℕ → Set SpectralCircle)
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (hUμ : ∀ n, greedySpectralMeasure U n ≪ μ.restrict (A n))
    (hμU : ∀ n, μ.restrict (A n) ≪ greedySpectralMeasure U n)
    (hVν : ∀ n, greedySpectralMeasure V n ≪ ν.restrict (B n))
    (hνV : ∀ n, ν.restrict (B n) ≪ greedySpectralMeasure V n)
    (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ n, w {n} ≠ 0) :
    (∃ W : H ≃ₗᵢ[ℂ] H, ∀ x, W (U x) = V (W x)) ↔
      (multiplicityLayerCode μ A w ≪ multiplicityLayerCode ν B w ∧
        multiplicityLayerCode ν B w ≪ multiplicityLayerCode μ A w) := by
  let ρ := μ + ν
  let C := rnSupport μ ρ
  let D := rnSupport ν ρ
  let A' := supportedFamily A C
  let B' := supportedFamily B D
  have hC : MeasurableSet C := rnSupport_measurable μ ρ
  have hD : MeasurableSet D := rnSupport_measurable ν ρ
  have hA' : ∀ n, MeasurableSet (A' n) := supportedFamily_measurable A hA C hC
  have hB' : ∀ n, MeasurableSet (B' n) := supportedFamily_measurable B hB D hD
  have hμρ : μ ≪ ρ.restrict C ∧ ρ.restrict C ≪ μ :=
    rnSupport_measureClass μ ρ (Measure.AbsolutelyContinuous.rfl.add_right ν)
  have hνρ : ν ≪ ρ.restrict D ∧ ρ.restrict D ≪ ν :=
    rnSupport_measureClass ν ρ (Measure.AbsolutelyContinuous.rfl.add_right' μ)
  have hAρ (n : ℕ) : μ.restrict (A n) ≪ ρ.restrict (A' n) ∧
      ρ.restrict (A' n) ≪ μ.restrict (A n) :=
    restrict_measureClass_baseChange μ ρ C (A n) (hA n) hμρ.1 hμρ.2
  have hBρ (n : ℕ) : ν.restrict (B n) ≪ ρ.restrict (B' n) ∧
      ρ.restrict (B' n) ≪ ν.restrict (B n) :=
    restrict_measureClass_baseChange ν ρ D (B n) (hB n) hνρ.1 hνρ.2
  have hUρ (n : ℕ) : greedySpectralMeasure U n ≪ ρ.restrict (A' n) :=
    (hUμ n).trans (hAρ n).1
  have hρU (n : ℕ) : ρ.restrict (A' n) ≪ greedySpectralMeasure U n :=
    (hAρ n).2.trans (hμU n)
  have hVρ (n : ℕ) : greedySpectralMeasure V n ≪ ρ.restrict (B' n) :=
    (hVν n).trans (hBρ n).1
  have hρV (n : ℕ) : ρ.restrict (B' n) ≪ greedySpectralMeasure V n :=
    (hBρ n).2.trans (hνV n)
  have hrep := unitaryDominatedFiber_classification U ρ A' hUρ hρU V B' hVρ hρV hA' hB'
  have hcode := multiplicityLayerCode_classification ρ A' B' hA' hB' w hw
  have hcodeA := multiplicityLayerCode_baseChange μ ρ A hA C hC hμρ.1 hμρ.2 w hw
  have hcodeB := multiplicityLayerCode_baseChange ν ρ B hB D hD hνρ.1 hνρ.2 w hw
  constructor
  · intro hW
    have hmid := hcode.mpr (hrep.mp hW)
    exact ⟨hcodeA.1.trans (hmid.1.trans hcodeB.2),
      hcodeB.1.trans (hmid.2.trans hcodeA.2)⟩
  · rintro ⟨hAB,hBA⟩
    apply hrep.mpr
    apply hcode.mp
    exact ⟨hcodeA.2.trans (hAB.trans hcodeB.1),
      hcodeB.2.trans (hBA.trans hcodeA.1)⟩

end
end OperatorCoding

end Source56

/- Preserved source skeleton: UnitarySpectralCodeNonzero -/
section Source57
/-! The finite multiplicity code of a nonzero Hilbert space is nonzero,
so its probability normalization is legitimate. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace OperatorCoding

open MeasureUnitary

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

theorem cyclicSpan_zero (U : StrongUnitary H) : cyclicSpan U 0 = ⊥ := by
  apply bot_unique
  apply cyclicSpan_minimal U 0 ⊥ (by change IsClosed ({(0 : H)} : Set H); exact isClosed_singleton)
  intro n
  simp only [map_zero, Submodule.zero_mem]

theorem exists_greedyCyclicGenerator_ne_zero (U : StrongUnitary H) :
    ∃ n, greedyCyclicGenerator U n ≠ 0 := by
  by_contra h
  push_neg at h
  have hbot : greedyCyclicAllSpan U = ⊥ := by
    unfold greedyCyclicAllSpan
    simp_rw [h,cyclicSpan_zero]
    simp
  exact top_ne_bot ((greedyCyclicAllSpan_eq_top U).symm.trans hbot)

theorem exists_greedySpectralMeasure_ne_zero (U : StrongUnitary H) :
    ∃ n, greedySpectralMeasure U n ≠ 0 := by
  obtain ⟨n,hn⟩ := exists_greedyCyclicGenerator_ne_zero U
  refine ⟨n, ?_⟩
  intro hzero
  have hmass := representationVectorMeasure_mass_toReal (unitaryCircleRepresentation U)
    (greedyCyclicGenerator U n)
  change (greedySpectralMeasure U n Set.univ).toReal = ‖greedyCyclicGenerator U n‖ ^ 2 at hmass
  simp only [hzero,Measure.coe_zero,Pi.zero_apply,ENNReal.toReal_zero] at hmass
  apply hn
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (greedyCyclicGenerator U n)]

theorem support_subset_multiplicityLayer_zero {X : Type*} [MeasurableSpace X]
    (A : ℕ → Set X) (i : ℕ) : A i ⊆ multiplicityLayer A 0 := by
  classical
  intro x hx
  simp only [multiplicityLayer,mem_setOf_eq,Nat.cast_zero]
  have hle : (1 : ℝ≥0∞) ≤ fiberMultiplicity A x := by
    calc
      (1 : ℝ≥0∞) = (A i).indicator (fun _ => (1 : ℝ≥0∞)) x := by simp [hx]
      _ ≤ fiberMultiplicity A x := ENNReal.le_tsum i
  exact lt_of_lt_of_le zero_lt_one hle

theorem unitary_multiplicityLayerCode_ne_zero (U : StrongUnitary H)
    (μ : Measure SpectralCircle) [IsFiniteMeasure μ] (A : ℕ → Set SpectralCircle)
    (hA : ∀ n, MeasurableSet (A n))
    (hUμ : ∀ n, greedySpectralMeasure U n ≪ μ.restrict (A n))
    (w : Measure ℕ) [IsFiniteMeasure w] (hw : ∀ n, w {n} ≠ 0) :
    multiplicityLayerCode μ A w ≠ 0 := by
  intro hzero
  have hac : fiberRestrictedMeasure μ (multiplicityLayer A) ≪ multiplicityLayerCode μ A w :=
    (weightedFiberMeasure_measureClass_count μ (multiplicityLayer A) w hw).1
  rw [hzero,Measure.absolutelyContinuous_zero_iff] at hac
  have hLayer : μ.restrict (multiplicityLayer A 0) = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    have h := congrArg (fun M : Measure (SpectralCircle × ℕ) => M (Set.univ ×ˢ {(0 : ℕ)})) hac
    change fiberRestrictedMeasure μ (multiplicityLayer A) (Set.univ ×ˢ {(0 : ℕ)}) = 0 at h
    rw [fiberRestrictedMeasure_rectangle μ (multiplicityLayer A)
      (multiplicityLayer_measurable A hA) Set.univ MeasurableSet.univ 0] at h
    exact h
  obtain ⟨n,hn⟩ := exists_greedySpectralMeasure_ne_zero U
  apply hn
  apply Measure.absolutelyContinuous_zero_iff.mp
  have hnull : μ.restrict (A n) = 0 := by
    apply Measure.restrict_eq_zero.mpr
    apply measure_mono_null (support_subset_multiplicityLayer_zero A n)
    exact Measure.restrict_eq_zero.mp hLayer
  simpa only [hnull] using hUμ n

end
end OperatorCoding

end Source57

/- Preserved source skeleton: UnitarySpectralCodeBorel -/
section Source58
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

namespace OperatorCoding

open MeasureUnitary SpectralDomination

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

local instance _root_.OperatorCoding.instMeasurableSpace_unitarySpectralCodeBorel : MeasurableSpace H := borel _
local instance _root_.OperatorCoding.instBorelSpace_unitarySpectralCodeBorel : BorelSpace H := ⟨rfl⟩
local instance _root_.OperatorCoding.instMeasurableSpaceStrongUnitary_unitarySpectralCodeBorel : MeasurableSpace (StrongUnitary H) := borel _
local instance _root_.OperatorCoding.instBorelSpaceStrongUnitary_unitarySpectralCodeBorel : BorelSpace (StrongUnitary H) := ⟨rfl⟩

theorem greedyMultiplicity_joint_measurable :
    Measurable (fun p : StrongUnitary H × SpectralCircle => fiberMultiplicity (greedySpectralSupport p.1) p.2) := by
  classical
  apply Measurable.ennreal_tsum
  intro n
  exact Measurable.ite (greedySpectralSupport_joint_measurableSet n) measurable_const measurable_const

def greedyLayerRegion : Set (StrongUnitary H × (SpectralCircle × ℕ)) :=
  {p | p.2.1 ∈ multiplicityLayer (greedySpectralSupport p.1) p.2.2}

theorem greedyLayerRegion_measurableSet : MeasurableSet (greedyLayerRegion (H := H)) := by
  change MeasurableSet {p : StrongUnitary H × (SpectralCircle × ℕ) |
    (p.2.2 : ℝ≥0∞) < fiberMultiplicity (greedySpectralSupport p.1) p.2.1}
  apply measurableSet_lt
  · exact (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
      (measurable_snd.comp measurable_snd)
  · exact greedyMultiplicity_joint_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

def greedyCodeKernel (w : Measure ℕ) [IsFiniteMeasure w] :
    Kernel (StrongUnitary H) (SpectralCircle × ℕ) := by
  classical
  exact (greedyDominatingKernel.prod (Kernel.const _ w)).withDensity
    (fun U p => (greedyLayerRegion (H := H)).indicator (fun _ => 1) (U,p))

theorem greedyCodeKernel_apply (w : Measure ℕ) [IsFiniteMeasure w] (U : StrongUnitary H) :
    greedyCodeKernel w U = multiplicityLayerCode (greedyDominatingKernel U) (greedySpectralSupport U) w := by
  classical
  have hd : Measurable (Function.uncurry (fun (U : StrongUnitary H) (p : SpectralCircle × ℕ) =>
      (greedyLayerRegion (H := H)).indicator (fun _ => (1 : ℝ≥0∞)) (U,p))) :=
    measurable_const.indicator (greedyLayerRegion_measurableSet (H := H))
  rw [greedyCodeKernel, Kernel.withDensity_apply _ hd]
  rw [Kernel.prod_apply, Kernel.const_apply]
  change ((greedyDominatingKernel U).prod w).withDensity
    ((measureFiberSet (multiplicityLayer (greedySpectralSupport U))).indicator (fun _ => 1)) = _
  exact withDensity_indicator_one
    (measureFiberSet_measurable _ (multiplicityLayer_measurable _ (greedySpectralSupport_measurableSet U)))

instance greedyCodeKernel_finite (w : Measure ℕ) [IsFiniteMeasure w] :
    IsFiniteKernel (greedyCodeKernel (H := H) w) := by
  classical
  unfold greedyCodeKernel
  apply Kernel.isFiniteKernel_withDensity_of_bounded _ (B := 1) (by simp)
  intro U p
  simp only [Set.indicator_apply]
  split_ifs <;> simp

theorem greedyCodeKernel_ne_zero (w : Measure ℕ) [IsFiniteMeasure w]
    (hw : ∀ n, w {n} ≠ 0) (U : StrongUnitary H) : greedyCodeKernel w U ≠ 0 := by
  rw [greedyCodeKernel_apply]
  exact unitary_multiplicityLayerCode_ne_zero U (greedyDominatingKernel U)
    (greedySpectralSupport U) (greedySpectralSupport_measurableSet U)
    (fun n => (greedySpectralSupport_equivalent U n).1) w hw

theorem greedyCodeKernel_classification (w : Measure ℕ) [IsFiniteMeasure w]
    (hw : ∀ n, w {n} ≠ 0) (U V : StrongUnitary H) :
    (∃ W : H ≃ₗᵢ[ℂ] H, ∀ x, W (U x) = V (W x)) ↔
      (greedyCodeKernel w U ≪ greedyCodeKernel w V ∧ greedyCodeKernel w V ≪ greedyCodeKernel w U) := by
  rw [greedyCodeKernel_apply, greedyCodeKernel_apply]
  exact unitary_multiplicityLayerCode_classification U V _ _ _ _
    (greedySpectralSupport_measurableSet U) (greedySpectralSupport_measurableSet V)
    (fun n => (greedySpectralSupport_equivalent U n).1)
    (fun n => (greedySpectralSupport_equivalent U n).2)
    (fun n => (greedySpectralSupport_equivalent V n).1)
    (fun n => (greedySpectralSupport_equivalent V n).2) w hw

end OperatorCoding

end
end Source58

/- Preserved source skeleton: UnitarySpectralReduction -/
section Source59
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace OperatorCoding

open MeasureUnitary SpectralDomination

def spectralCountingWeight : Measure ℕ :=
  Measure.sum (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n • Measure.dirac n)

instance spectralCountingWeight_finite : IsFiniteMeasure spectralCountingWeight := by
  constructor
  simp only [spectralCountingWeight, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  rw [ENNReal.tsum_geometric_two]
  norm_num

theorem spectralCountingWeight_singleton_ne_zero (n : ℕ) : spectralCountingWeight {n} ≠ 0 := by
  have hle := Measure.le_sum (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ k • Measure.dirac k) n
  have hmass := Measure.le_iff'.mp hle {n}
  have hp : 0 < ((2⁻¹ : ℝ≥0∞) ^ n • Measure.dirac n) {n} := by
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_singleton n), mul_one]
    exact pos_iff_ne_zero.mpr (pow_ne_zero n (by simp))
  exact ne_of_gt (hp.trans_le hmass)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] [SecondCountableTopology H]

local instance _root_.OperatorCoding.instMeasurableSpace_unitarySpectralReduction : MeasurableSpace H := borel _
local instance _root_.OperatorCoding.instBorelSpace_unitarySpectralReduction : BorelSpace H := ⟨rfl⟩
local instance _root_.OperatorCoding.instMeasurableSpaceStrongUnitary_unitarySpectralReduction : MeasurableSpace (StrongUnitary H) := borel _
local instance _root_.OperatorCoding.instBorelSpaceStrongUnitary_unitarySpectralReduction : BorelSpace (StrongUnitary H) := ⟨rfl⟩

def unitaryCantorProbability (U : StrongUnitary H) : ProbabilityMeasure Cantor :=
  cantorKernelProbability (greedyCodeKernel spectralCountingWeight)
    (greedyCodeKernel_ne_zero spectralCountingWeight spectralCountingWeight_singleton_ne_zero) U

theorem unitaryCantorProbability_measurable : Measurable (unitaryCantorProbability (H := H)) :=
  cantorKernelProbability_measurable _ _

theorem unitaryCantorProbability_classification (U V : StrongUnitary H) :
    ElementConjugate U V ↔ MeasureEquivalent (unitaryCantorProbability U) (unitaryCantorProbability V) := by
  have hcode := greedyCodeKernel_classification spectralCountingWeight spectralCountingWeight_singleton_ne_zero U V
  have hnorm := cantorKernelProbability_classification (greedyCodeKernel spectralCountingWeight)
    (greedyCodeKernel_ne_zero spectralCountingWeight spectralCountingWeight_singleton_ne_zero) U V
  change ElementConjugate U V ↔
    ((cantorKernelProbability _ _ U : Measure Cantor) ≪ cantorKernelProbability _ _ V ∧
      (cantorKernelProbability _ _ V : Measure Cantor) ≪ cantorKernelProbability _ _ U)
  rw [hnorm]
  rw [← hcode]
  constructor
  · rintro ⟨W,hW⟩
    refine ⟨W,fun x => ?_⟩
    have he := congrArg (fun T : StrongUnitary H => T (W x)) hW
    simpa using he
  · rintro ⟨W,hW⟩
    refine ⟨W,?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    change W (U (W.symm x)) = V x
    rw [hW, W.apply_symm_apply]

theorem unitaries_borelReduce_measureEquivalence :
    BorelReducesWith (borel (StrongUnitary H)) inferInstance ElementConjugate MeasureEquivalent :=
  ⟨unitaryCantorProbability, unitaryCantorProbability_measurable, unitaryCantorProbability_classification⟩

instance spectralCanonicalHilbert_nontrivial : Nontrivial CanonicalHilbert := by
  refine ⟨⟨0, lp.single 2 0 (1 : ℂ), ?_⟩⟩
  intro h
  have he := congrArg (fun v : CanonicalHilbert => v 0) h
  change (0 : ℂ) = 1 at he
  exact zero_ne_one he

theorem cyclicRepresentations_borelReduce_measureEquivalence :
    BorelReducesWith (unitaryRepresentationBorel (Multiplicative ℤ)) inferInstance
      UnitaryRepresentationEquivalent MeasureEquivalent :=
  borelReducesWith_trans cyclicRepresentations_borelBireducible_unitaries.1
    unitaries_borelReduce_measureEquivalence

end OperatorCoding

end
end Source59

/- Preserved source skeleton: BenchmarkOperatorTransport -/
section Source60
open MeasureTheory

noncomputable section

namespace BenchmarkComparisons

def representationToHom {Γ : Type*} [Group Γ] (ρ : Representation Γ) :
    OperatorCoding.UnitaryRepresentation Γ where
  toFun := ρ.operator
  map_one' := by apply LinearIsometryEquiv.ext; intro v; exact ρ.map_one v
  map_mul' := by intro g h; apply LinearIsometryEquiv.ext; intro v; exact ρ.map_mul g h v

def representationFromHom {Γ : Type*} [Group Γ] (ρ : OperatorCoding.UnitaryRepresentation Γ) :
    Representation Γ where
  operator := ρ
  map_one := by intro v; simp
  map_mul := by intro g h v; simp

def representationEquiv (Γ : Type*) [Group Γ] :
    Representation Γ ≃ OperatorCoding.UnitaryRepresentation Γ where
  toFun := representationToHom
  invFun := representationFromHom
  left_inv := by intro ρ; cases ρ; rfl
  right_inv := by intro ρ; ext g v; rfl

theorem continuous_representationToHom (Γ : Type*) [Group Γ] :
    @Continuous (Representation Γ) (OperatorCoding.UnitaryRepresentation Γ)
      (representationStrongTopology Γ) (OperatorCoding.unitaryRepresentationTopology Γ)
      representationToHom := by
  letI : TopologicalSpace (Representation Γ) := representationStrongTopology Γ
  letI : TopologicalSpace (OperatorCoding.UnitaryRepresentation Γ) :=
    OperatorCoding.unitaryRepresentationTopology Γ
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro g
  apply (OperatorCoding.strongUnitary_continuous_iff _).mpr
  intro v
  have hc : Continuous (fun ρ : Representation Γ => fun g : Γ => fun v : Hilbert => ρ.operator g v) :=
    continuous_induced_dom
  exact (continuous_apply v).comp ((continuous_apply g).comp hc)

theorem continuous_representationFromHom (Γ : Type*) [Group Γ] :
    @Continuous (OperatorCoding.UnitaryRepresentation Γ) (Representation Γ)
      (OperatorCoding.unitaryRepresentationTopology Γ) (representationStrongTopology Γ)
      representationFromHom := by
  letI : TopologicalSpace (Representation Γ) := representationStrongTopology Γ
  letI : TopologicalSpace (OperatorCoding.UnitaryRepresentation Γ) :=
    OperatorCoding.unitaryRepresentationTopology Γ
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro g
  apply continuous_pi
  intro v
  exact (OperatorCoding.strongUnitary_continuous_eval v).comp
    ((continuous_apply g).comp continuous_induced_dom)

theorem representationEquivalent_iff {Γ : Type*} [Group Γ] (ρ σ : Representation Γ) :
    RepresentationEquivalent ρ σ ↔
      OperatorCoding.UnitaryRepresentationEquivalent (representationToHom ρ) (representationToHom σ) := by
  constructor
  · rintro ⟨U,hU⟩
    refine ⟨U,fun g => ?_⟩
    apply LinearIsometryEquiv.ext
    intro v
    change U (ρ.operator g (U.symm v)) = σ.operator g v
    rw [hU]
    simp
  · rintro ⟨U,hU⟩
    refine ⟨U,fun g v => ?_⟩
    have h := congrArg (fun W : OperatorCoding.StrongUnitary OperatorCoding.CanonicalHilbert => W (U v)) (hU g)
    simpa using h

theorem representations_borelBireducible (Γ : Type*) [Group Γ] :
    BorelBireducibleWith (representationBorel Γ) (OperatorCoding.unitaryRepresentationBorel Γ)
      RepresentationEquivalent OperatorCoding.UnitaryRepresentationEquivalent := by
  constructor
  · refine ⟨representationToHom, ?_, representationEquivalent_iff⟩
    exact @Continuous.borel_measurable _ _ (representationStrongTopology Γ)
      (OperatorCoding.unitaryRepresentationTopology Γ) _ (continuous_representationToHom Γ)
  · refine ⟨representationFromHom, ?_, ?_⟩
    · exact @Continuous.borel_measurable _ _ (OperatorCoding.unitaryRepresentationTopology Γ)
        (representationStrongTopology Γ) _ (continuous_representationFromHom Γ)
    · intro ρ σ
      simpa only [(representationEquiv Γ).apply_symm_apply] using
        (representationEquivalent_iff (representationFromHom ρ) (representationFromHom σ)).symm













end BenchmarkComparisons

end
end Source60

open BenchmarkComparisons in
theorem solution :
    BorelReducesWith (representationBorel (Multiplicative ℤ)) inferInstance
      RepresentationEquivalent MeasureEquivalent :=
  OperatorCoding.borelReducesWith_trans
    (representations_borelBireducible (Multiplicative ℤ)).1
    OperatorCoding.cyclicRepresentations_borelReduce_measureEquivalence

#print axioms solution
