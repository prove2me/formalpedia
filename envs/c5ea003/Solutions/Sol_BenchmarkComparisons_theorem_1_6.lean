-- Prove2me | solution 1 for BenchmarkComparisons.theorem_1_6
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:57:14.619026+00:00
-- url     : https://prove2.me/submissions/456320b8-39cb-491e-b4a0-2bbdbdc2fbc9

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorAmplified
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorBorel
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureGramSchmidtBorel
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryMultipliers
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryRN
import Definitions.Def_BenchmarkOperator20261026_MeasureVariableGramSchmidt
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Definitions.Def_BenchmarkOperator20261026_OperatorUnitaryBorel
import Definitions.Def_BenchmarkRelations
import Init
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.CantorSet
import Theorems.Thm_BenchmarkComparisons_cyclic_representations_borelReduces_measure
import Theorems.Thm_BenchmarkComparisons_free_representations_borelBireducible_operators
import Theorems.Thm_BenchmarkComparisons_theorem_1_5

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

/- Preserved source skeleton: HilbertSequenceTopology -/
section Source1
/-! The canonical Hilbert space has its actual norm Polish topology;
its coordinate map is a measurable embedding for this topology. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace OperatorCoding

noncomputable section











theorem canonicalHilbert_coordinates_continuous :
    Continuous (fun x : CanonicalHilbert => (x : ℕ → ℂ)) := by
  apply continuous_pi
  intro i
  exact (lp.lipschitzWith_one_eval (E := fun _ : ℕ => ℂ) 2 i).continuous

theorem canonicalHilbert_coordinates_measurableEmbedding :
    @MeasurableEmbedding CanonicalHilbert (ℕ → ℂ) (borel CanonicalHilbert)
      inferInstance (fun x => (x : ℕ → ℂ)) := by
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  exact canonicalHilbert_coordinates_continuous.measurableEmbedding (fun _ _ h => lp.ext h)

end
end OperatorCoding

end Source1

/- Preserved source skeleton: MeasureGramSchmidtBorel -/
section Source2
/-! Borel Gram–Schmidt and Borel removal of its zero vectors.
These are fixed-fiber results; a parameter-dependent L² trivialization still
requires a measurable dense fundamental family. -/

open MeasureTheory InnerProductSpace Set Finset

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]





theorem measurable_nat_count (p : S → ℕ → Prop) [∀ s, DecidablePred (p s)]
    (hp : ∀ n, MeasurableSet {s | p s n}) (n : ℕ) :
    Measurable (fun s => Nat.count (p s) n) := by
  induction n with
  | zero => simpa only [Nat.count_zero] using (measurable_const : Measurable (fun _ : S => (0 : ℕ)))
  | succ n ih =>
    simp_rw [Nat.count_succ]
    exact ih.add (Measurable.ite (hp n) measurable_const measurable_const)

theorem measurable_nat_nth (p : S → ℕ → Prop) [∀ s, DecidablePred (p s)]
    (hp : ∀ n, MeasurableSet {s | p s n}) (hinf : ∀ s, {n | p s n}.Infinite) (n : ℕ) :
    Measurable (fun s => Nat.nth (p s) n) := by
  apply measurable_to_countable'
  intro m
  have heq : {s | Nat.nth (p s) n = m} = {s | p s m} ∩ {s | Nat.count (p s) m = n} := by
    ext s
    constructor
    · intro h
      exact ⟨h ▸ Nat.nth_mem_of_infinite (hinf s) n,
        h ▸ Nat.count_nth_of_infinite (hinf s) n⟩
    · rintro ⟨hm, hc⟩
      rw [← hc]
      exact Nat.nth_count hm
  change MeasurableSet {s | Nat.nth (p s) n = m}
  rw [heq]
  exact (hp m).inter (measurableSet_eq_fun (measurable_nat_count p hp m) measurable_const)

















end MeasureUnitary

end Source2

/- Preserved source skeleton: MeasureUnitaryMultipliers -/
section Source3
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

end Source3

/- Preserved source skeleton: MeasureCantorTuple -/
section Source4
/-! Countably many genuine L² multiplication unitaries, one for every
clopen finite-coordinate Cantor cylinder. Equivalent measures give
intertwining representations through the actual RN unitary. -/

open MeasureTheory Set

namespace MeasureUnitary


























theorem cantorCylinder_isPiSystem : IsPiSystem (Set.range cantorCylinder) := by
  rw [cantorCylinder_range]
  exact isPiSystem_measurableCylinders

end MeasureUnitary

end Source4

/- Preserved source skeleton: MeasureUnitaryDensity -/
section Source5
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







theorem constantVectorL2_density [IsFiniteMeasure μ] (v : E) (hv : ‖v‖ = 1) :
    vectorDensityMeasure μ (constantVectorL2 μ v) = μ := by
  unfold vectorDensityMeasure
  have h : (fun x => ENNReal.ofReal (‖constantVectorL2 μ v x‖ ^ 2)) =ᵐ[μ] fun _ => 1 := by
    filter_upwards [constantVectorL2_coe μ v] with x hx
    rw [hx, hv]
    norm_num
  rw [withDensity_congr_ae h]
  change μ.withDensity 1 = μ
  exact withDensity_one







end MeasureUnitary

end Source5

/- Preserved source skeleton: MeasureCantorAmplified -/
section Source6
/-! An infinite-multiplicity Cantor representation, on Hilbert-valued L².
The coefficient Hilbert space is fixed, but the measure-dependent L² spaces
are not yet identified with one canonical Hilbert space in a Borel fashion. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]





theorem equivalentMeasures_vectorCantorMultiplierEquivalent (μ ν : Measure CantorSpace)
    [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    VectorCantorMultiplierEquivalent E μ ν := by
  refine ⟨rnWeightedEquiv μ ν hμν hνμ, fun k f => ?_⟩
  exact rnWeightedEquiv_intertwines_phase μ (cantorCylinderPhase k)
    (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) ν hμν hνμ f

theorem indicatorL2_vectorCantorMultiplier (μ : Measure CantorSpace) (k : CantorCylinderIndex)
    (f : Lp E 2 μ) :
    indicatorL2 μ (cantorCylinder_measurable k) f =
      (1 / 2 : ℂ) • (f + vectorCantorMultiplier μ k f) := by
  change indicatorL2 μ (cantorCylinder_measurable k) f =
    (1 / 2 : ℂ) • (f + phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f)
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ (cantorCylinder_measurable k) f,
    Lp.coeFn_smul (1 / 2 : ℂ) (f + phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f),
    Lp.coeFn_add f (phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f),
    phaseMap_coe μ (cantorCylinderPhase k) (cantorCylinderPhase_measurable k)
      (cantorCylinderPhase_norm k) f] with x hI hs ha hp
  simp only [Pi.smul_apply, Pi.add_apply] at hs ha
  rw [hI, hs, ha, hp]
  classical
  by_cases hxs : x ∈ cantorCylinder k
  · simp only [cantorCylinderPhase, if_pos hxs, indicator_of_mem hxs, one_smul]
    rw [← two_smul ℂ (f x), smul_smul]
    norm_num
  · simp only [cantorCylinderPhase, if_neg hxs, indicator_of_notMem hxs, neg_one_smul,
      add_neg_cancel, smul_zero]

theorem vectorCantorMultiplier_intertwines_indicators (μ ν : Measure CantorSpace)
    (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f))
    (k : CantorCylinderIndex) (f : Lp E 2 μ) :
    U (indicatorL2 μ (cantorCylinder_measurable k) f) =
      indicatorL2 ν (cantorCylinder_measurable k) (U f) := by
  rw [indicatorL2_vectorCantorMultiplier, U.map_smul, U.map_add, hU,
    ← indicatorL2_vectorCantorMultiplier]

theorem vectorCantorMultiplier_intertwiner_density (μ ν : Measure CantorSpace) [IsFiniteMeasure μ]
    (v : E) (hv : ‖v‖ = 1) (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f)) :
    μ = vectorDensityMeasure ν (U (constantVectorL2 μ v)) := by
  have hmass : ∀ k : CantorCylinderIndex,
      μ (cantorCylinder k) = vectorDensityMeasure ν (U (constantVectorL2 μ v)) (cantorCylinder k) := by
    intro k
    calc
      μ (cantorCylinder k) = vectorDensityMeasure μ (constantVectorL2 μ v) (cantorCylinder k) := by
        rw [constantVectorL2_density μ v hv]
      _ = ENNReal.ofReal (‖indicatorL2 μ (cantorCylinder_measurable k) (constantVectorL2 μ v)‖ ^ 2) :=
        vectorDensityMeasure_apply _ _ _
      _ = ENNReal.ofReal (‖indicatorL2 ν (cantorCylinder_measurable k) (U (constantVectorL2 μ v))‖ ^ 2) := by
        rw [← vectorCantorMultiplier_intertwines_indicators μ ν U hU, U.norm_map]
      _ = vectorDensityMeasure ν (U (constantVectorL2 μ v)) (cantorCylinder k) :=
        (vectorDensityMeasure_apply _ _ _).symm
  apply ext_of_generate_finite (Set.range cantorCylinder) cantorCylinder_generates.symm
    cantorCylinder_isPiSystem
  · rintro s ⟨k, rfl⟩
    exact hmass k
  · have h := hmass (⟨∅, Set.univ⟩ : CantorCylinderIndex)
    simpa [cantorCylinder, cylinder] using h

theorem vectorCantorMultiplier_intertwiner_absolutelyContinuous (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] (v : E) (hv : ‖v‖ = 1) (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f)) : μ ≪ ν := by
  rw [vectorCantorMultiplier_intertwiner_density μ ν v hv U hU]
  exact vectorDensityMeasure_absolutelyContinuous ν _

theorem vectorCantorMultiplierEquivalent_iff (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (v : E) (hv : ‖v‖ = 1) :
    VectorCantorMultiplierEquivalent E μ ν ↔ μ ≪ ν ∧ ν ≪ μ := by
  constructor
  · rintro ⟨U, hU⟩
    constructor
    · exact vectorCantorMultiplier_intertwiner_absolutelyContinuous μ ν v hv U hU
    · apply vectorCantorMultiplier_intertwiner_absolutelyContinuous ν μ v hv U.symm
      intro k f
      apply U.injective
      simpa using (hU k (U.symm f)).symm
  · intro h
    exact equivalentMeasures_vectorCantorMultiplierEquivalent μ ν h.1 h.2



theorem canonicalHilbertUnitVector_norm : ‖canonicalHilbertUnitVector‖ = 1 := by
  change ‖(lp.single 2 0 (1 : ℂ) : OperatorCoding.CanonicalHilbert)‖ = 1
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

theorem amplifiedCantorMultiplierEquivalent_iff (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    VectorCantorMultiplierEquivalent OperatorCoding.CanonicalHilbert μ ν ↔ μ ≪ ν ∧ ν ≪ μ :=
  vectorCantorMultiplierEquivalent_iff μ ν canonicalHilbertUnitVector canonicalHilbertUnitVector_norm

end MeasureUnitary

end Source6

/- Preserved source skeleton: MeasureCantorGram -/
section Source7
/-! Measurable Gram matrices for the explicit varying-measure L² family.
The parameter measurable structure is the genuine Giry structure on
probability measures, and all entries are actual L² inner products. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

theorem cantorFundamentalVector_inner (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (k l : CantorFundamentalIndex) :
    inner ℂ (cantorFundamentalVector μ k) (cantorFundamentalVector μ l) =
      μ.real (cantorCylinder k.1 ∩ cantorCylinder l.1) •
        inner ℂ (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)
          (lp.single 2 l.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert) :=
  L2.inner_indicatorConstLp_indicatorConstLp (cantorCylinder_measurable k.1)
    (cantorCylinder_measurable l.1) (measure_ne_top μ _) (measure_ne_top μ _) _ _

theorem measurable_cantorFundamentalVector_inner (k l : CantorFundamentalIndex) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalVector (μ : Measure CantorSpace) k)
        (cantorFundamentalVector (μ : Measure CantorSpace) l)) := by
  simp only [cantorFundamentalVector_inner, measureReal_def]
  exact (((Measure.measurable_coe ((cantorCylinder_measurable k.1).inter
    (cantorCylinder_measurable l.1))).comp measurable_subtype_coe).ennreal_toReal).smul measurable_const

theorem measurable_cantorFundamentalSequence_inner (i j : ℕ) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalSequence (μ : Measure CantorSpace) i)
        (cantorFundamentalSequence (μ : Measure CantorSpace) j)) :=
  measurable_cantorFundamentalVector_inner (cantorFundamentalEnumeration i) (cantorFundamentalEnumeration j)













end MeasureUnitary

end Source7

/- Preserved source skeleton: MeasureVariableGramSchmidt -/
section Source8
/-! Gram–Schmidt in genuinely varying Hilbert fibers. Measurability is
deduced from scalar Gram entries, without putting a fictitious common
topology on the different L² spaces. Every constructed section is an actual
finite linear combination of the fundamental sections. -/

open MeasureTheory InnerProductSpace Set

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : S → Type*} [∀ s, NormedAddCommGroup (E s)] [∀ s, InnerProductSpace ℂ (E s)]



theorem finiteBorelSection_raw (f : ∀ s, ℕ → E s) (n : ℕ) :
    FiniteBorelSection f (fun s => f s n) := by
  refine ⟨Unit, inferInstance, (fun _ => n), (fun _ _ => 1),
    (fun _ => measurable_const), ?_⟩
  intro s
  simp

theorem finiteBorelSection_zero (f : ∀ s, ℕ → E s) :
    FiniteBorelSection f (fun s => (0 : E s)) := by
  refine ⟨Empty, inferInstance, Empty.elim, (fun _ => Empty.elim),
    (fun i => Empty.elim i), ?_⟩
  intro s
  simp

theorem FiniteBorelSection.add {f : ∀ s, ℕ → E s} {v w : ∀ s, E s}
    (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    FiniteBorelSection f (fun s => v s + w s) := by
  classical
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  obtain ⟨J, hJ, k, d, hd, hw⟩ := hw
  letI := hI
  letI := hJ
  refine ⟨I ⊕ J, inferInstance, Sum.elim j k, (fun s => Sum.elim (c s) (d s)), ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hd i
  · intro s
    dsimp only
    rw [Fintype.sum_sum_type, hv s, hw s]
    rfl

theorem FiniteBorelSection.smul {f : ∀ s, ℕ → E s} {v : ∀ s, E s}
    (hv : FiniteBorelSection f v) {a : S → ℂ} (ha : Measurable a) :
    FiniteBorelSection f (fun s => a s • v s) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  letI := hI
  refine ⟨I, hI, j, (fun s i => a s * c s i), (fun i => ha.mul (hc i)), ?_⟩
  intro s
  dsimp only
  rw [hv s, Finset.smul_sum]
  simp only [smul_smul]

theorem FiniteBorelSection.neg {f : ∀ s, ℕ → E s} {v : ∀ s, E s}
    (hv : FiniteBorelSection f v) : FiniteBorelSection f (fun s => -v s) := by
  simpa only [neg_one_smul] using hv.smul (a := fun _ => (-1 : ℂ)) measurable_const

theorem FiniteBorelSection.sub {f : ∀ s, ℕ → E s} {v w : ∀ s, E s}
    (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    FiniteBorelSection f (fun s => v s - w s) := by
  simpa only [sub_eq_add_neg] using hv.add hw.neg

theorem finiteBorelSection_sum {f : ∀ s, ℕ → E s} {I : Type*}
    (t : Finset I) (v : I → ∀ s, E s) (hv : ∀ i ∈ t, FiniteBorelSection f (v i)) :
    FiniteBorelSection f (fun s => ∑ i ∈ t, v i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using finiteBorelSection_zero f
  | @insert i t hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hv i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

theorem FiniteBorelSection.inner_measurable {f : ∀ s, ℕ → E s}
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    {v w : ∀ s, E s} (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    Measurable (fun s => inner ℂ (v s) (w s)) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  obtain ⟨J, hJ, k, d, hd, hw⟩ := hw
  letI := hI
  letI := hJ
  have heq : (fun s => inner ℂ (v s) (w s)) =
      fun s => ∑ i : I, ∑ l : J, d s l * ((starRingEnd ℂ) (c s i) * inner ℂ (f s (j i)) (f s (k l))) := by
    funext s
    rw [hv s, hw s, sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
  rw [heq]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro l hl
  exact (hd l).mul ((Complex.continuous_conj.measurable.comp (hc i)).mul (hgram (j i) (k l)))

theorem FiniteBorelSection.norm_measurable {f : ∀ s, ℕ → E s}
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    {v : ∀ s, E s} (hv : FiniteBorelSection f v) : Measurable (fun s => ‖v s‖) := by
  have hm := (Complex.continuous_re.measurable.comp (hv.inner_measurable hgram hv)).sqrt
  convert hm using 1
  funext s
  change ‖v s‖ = Real.sqrt (RCLike.re (inner ℂ (v s) (v s)))
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ), Real.sqrt_sq (norm_nonneg _)]

theorem variableGramSchmidt_finiteBorelSection (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    FiniteBorelSection f (fun s => gramSchmidt ℂ (f s) n) := by
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
    apply (finiteBorelSection_raw f n).sub
    apply finiteBorelSection_sum
    intro i hi
    have hg := ih i (Finset.mem_Iio.mp hi)
    apply hg.smul
    exact (hg.inner_measurable hgram (finiteBorelSection_raw f n)).div
      (Complex.continuous_ofReal.measurable.comp ((hg.norm_measurable hgram).pow_const 2))

theorem variableGramSchmidtNormed_finiteBorelSection (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    FiniteBorelSection f (fun s => gramSchmidtNormed ℂ (f s) n) := by
  have hg := variableGramSchmidt_finiteBorelSection f hgram n
  exact hg.smul ((Complex.continuous_ofReal.measurable.comp (hg.norm_measurable hgram)).inv)



theorem variableGramSchmidtNormed_norm_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    Measurable (fun s => ‖gramSchmidtNormed ℂ (f s) n‖) :=
  (variableGramSchmidtNormed_finiteBorelSection f hgram n).norm_measurable hgram

theorem variableGramSchmidtNormed_nonzero_measurableSet (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    MeasurableSet {s | gramSchmidtNormed ℂ (f s) n ≠ 0} := by
  have h := (variableGramSchmidtNormed_norm_measurable f hgram n) (measurableSet_singleton (0 : ℝ))
  simpa only [Set.preimage, Set.mem_singleton_iff, norm_eq_zero] using h.compl







end MeasureUnitary

end Source8

/- Preserved source skeleton: OperatorUnitaryBorel -/
section Source9
/-! The strong topology on the unitary group is determined by countably
many dense vector evaluations. This identifies its Borel structure without
using operator-norm measurability in place of strong measurability. -/

open Filter Topology TopologicalSpace

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]



variable {H}







theorem strongUnitary_measurable_of_evaluations {X : Type*} [MeasurableSpace X]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : X → StrongUnitary H) (hf : ∀ x : H, Measurable (fun a => f a x)) :
    @Measurable X (StrongUnitary H) inferInstance (borel (StrongUnitary H)) f := by
  apply measurable_iff_comap_le.mpr
  change (borel (StrongUnitary H)).comap f ≤ (inferInstance : MeasurableSpace X)
  rw [strongUnitary_topology_eq_dense, borel_comap]
  rw [MeasurableSpace.comap_comp]
  have hb : (inferInstance : MeasurableSpace (ℕ → H)) = borel (ℕ → H) := BorelSpace.measurable_eq
  rw [← hb]
  exact measurable_iff_comap_le.mp (measurable_pi_iff.mpr (fun n => hf (denseSeq H n)))



end OperatorCoding

end Source9

/- Preserved source skeleton: MeasureCantorBorel -/
section Source10
/-! The genuine fixed-Hilbert Borel realization of the amplified
Cantor-cylinder multiplication representations. -/

open MeasureTheory Set Filter InnerProductSpace OperatorCoding
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

attribute [local instance] _root_.MeasureUnitary.instMeasurableSpaceSubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCantorBorel
local instance _root_.MeasureUnitary.instBorelSpaceSubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCantorBorel : BorelSpace CanonicalHilbert := ⟨rfl⟩







theorem cantorFiberBasis_apply (μ : ProbabilityMeasure CantorSpace) (n : ℕ) :
    cantorFiberBasis (μ : Measure CantorSpace) n = variableSelectedGramSchmidt
      (fun ν : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (ν : Measure CantorSpace)) μ n := by
  unfold cantorFiberBasis
  rw [HilbertBasis.coe_mk]
  rfl









theorem strongUnitary_measurable_evaluations_of_basis {S : Type*} [MeasurableSpace S]
    (U : S → StrongUnitary CanonicalHilbert)
    (hU : ∀ j : ℕ, Measurable (fun s => U s (lp.single 2 j (1 : ℂ) : CanonicalHilbert)))
    (x : CanonicalHilbert) : Measurable (fun s => U s x) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n s => ∑ j ∈ Finset.range n, (x j) • U s (lp.single 2 j (1 : ℂ) : CanonicalHilbert))
  · intro n
    exact (Finset.range n).measurable_sum (fun j hj => (hU j).const_smul (x j))
  · apply tendsto_pi_nhds.mpr
    intro s
    have hsum := ((U s).toContinuousLinearEquiv.toContinuousLinearMap.hasSum
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x)).tendsto_sum_nat
    convert hsum using 1
    funext n
    apply Finset.sum_congr rfl
    intro j hj
    have he : (lp.single 2 j (x j) : CanonicalHilbert) =
        (x j) • (lp.single 2 j (1 : ℂ) : CanonicalHilbert) := by
      simpa using (lp.single_smul (E := fun _ : ℕ => ℂ) 2 j (x j) (1 : ℂ))
    rw [he, map_smul]
    rfl



end

end MeasureUnitary

end Source10

/- Preserved source skeleton: MeasureCantorCircle -/
section Source11
/-! An explicit continuous injection of Cantor space into a short circle
arc, with an actual continuous inverse on its image. -/

open MeasureTheory Set

namespace MeasureUnitary

noncomputable section

def cantorRealCoordinate (x : CantorSpace) : ℝ := cantorSetHomeomorphNatToBool.symm x

theorem cantorRealCoordinate_continuous : Continuous cantorRealCoordinate :=
  continuous_subtype_val.comp cantorSetHomeomorphNatToBool.symm.continuous

theorem cantorRealCoordinate_bounds (x : CantorSpace) :
    0 ≤ cantorRealCoordinate x ∧ cantorRealCoordinate x ≤ 1 :=
  cantorSet_subset_unitInterval (cantorSetHomeomorphNatToBool.symm x).property

theorem cantorRealCoordinate_injective : Function.Injective cantorRealCoordinate := by
  intro x y h
  apply cantorSetHomeomorphNatToBool.symm.injective
  exact Subtype.ext h

def cantorCirclePhase (x : CantorSpace) : ℂ := Complex.exp (cantorRealCoordinate x * Complex.I)

theorem cantorCirclePhase_continuous : Continuous cantorCirclePhase :=
  Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp cantorRealCoordinate_continuous).mul continuous_const)

theorem cantorCirclePhase_norm (x : CantorSpace) : ‖cantorCirclePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem cantorCirclePhase_arg (x : CantorSpace) : (cantorCirclePhase x).arg = cantorRealCoordinate x := by
  rw [cantorCirclePhase, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  obtain ⟨h0, h1⟩ := cantorRealCoordinate_bounds x
  constructor <;> linarith [Real.pi_gt_three]

theorem cantorCirclePhase_injective : Function.Injective cantorCirclePhase := by
  intro x y h
  apply cantorRealCoordinate_injective
  simpa only [cantorCirclePhase_arg] using congrArg Complex.arg h

def cantorCircleContinuousMap : C(CantorSpace, ℂ) := ⟨cantorCirclePhase, cantorCirclePhase_continuous⟩

end

end MeasureUnitary

end Source11

/- Preserved source skeleton: MeasureContinuousMultipliers -/
section Source12
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

theorem continuousMultiplierL2_one : continuousMultiplierL2 (E := E) μ (1 : C(α, ℂ)) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousMultiplierL2_coe μ (1 : C(α, ℂ)) f] with x hx
  simpa using hx

theorem continuousMultiplierL2_mul (g h : C(α, ℂ)) :
    continuousMultiplierL2 (E := E) μ (g * h) = continuousMultiplierL2 μ g * continuousMultiplierL2 μ h := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousMultiplierL2_coe μ (g * h) f,
    continuousMultiplierL2_coe μ g (continuousMultiplierL2 μ h f), continuousMultiplierL2_coe μ h f]
    with x hgh hg hh
  change (continuousMultiplierL2 μ (g * h) f) x =
    (continuousMultiplierL2 μ g (continuousMultiplierL2 μ h f)) x
  rw [hgh, hg, hh]
  exact mul_smul _ _ _

theorem continuousMultiplierL2_algebraMap (c : ℂ) :
    continuousMultiplierL2 (E := E) μ (algebraMap ℂ C(α, ℂ) c) =
      algebraMap ℂ (Lp E 2 μ →L[ℂ] Lp E 2 μ) c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, continuousMultiplierL2_one,
    Algebra.algebraMap_eq_smul_one]

theorem continuousMultiplierL2_star (g : C(α, ℂ)) :
    continuousMultiplierL2 (E := E) μ (star g) = star (continuousMultiplierL2 (E := E) μ g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousMultiplierL2_coe μ (star g) f,
    continuousMultiplierL2_coe μ g h] with x hf hh
  rw [hf, hh]
  simp only [ContinuousMap.star_apply, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]

def continuousMultiplierStarAlgHom : C(α, ℂ) →⋆ₐ[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) where
  toFun := continuousMultiplierL2 μ
  map_zero' := map_zero _
  map_one' := continuousMultiplierL2_one μ
  map_add' := map_add _
  map_mul' := continuousMultiplierL2_mul μ
  commutes' := continuousMultiplierL2_algebraMap μ
  map_star' := continuousMultiplierL2_star μ

theorem continuousMultiplierL2_phase (c : C(α, ℂ)) (hnorm : ∀ x, ‖c x‖ = 1) (f : Lp E 2 μ) :
    continuousMultiplierL2 μ c f = phaseEquiv μ c c.continuous.measurable hnorm f := by
  apply Lp.ext
  exact (continuousMultiplierL2_coe μ c f).trans (phaseMap_coe μ c c.continuous.measurable hnorm f).symm

end

end MeasureUnitary

end Source12

/- Preserved source skeleton: MeasureVariableOperatorGram -/
section Source13
/-! Matrix measurability survives the varying-fiber Gram–Schmidt process
for any operator family with measurable fundamental matrix entries. The
operator images need not lie in a finite span of the fundamental family. -/

open MeasureTheory InnerProductSpace Set

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : S → Type*} [∀ s, NormedAddCommGroup (E s)] [∀ s, InnerProductSpace ℂ (E s)]

theorem FiniteBorelSection.operator_inner_measurable {f : ∀ s, ℕ → E s}
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ i j, Measurable (fun s => inner ℂ (f s i) (T s (f s j))))
    {v w : ∀ s, E s} (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    Measurable (fun s => inner ℂ (v s) (T s (w s))) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  obtain ⟨J, hJ, k, d, hd, hw⟩ := hw
  letI := hI
  letI := hJ
  have heq : (fun s => inner ℂ (v s) (T s (w s))) = fun s =>
      ∑ i : I, ∑ l : J, d s l * ((starRingEnd ℂ) (c s i) *
        inner ℂ (f s (j i)) (T s (f s (k l)))) := by
    funext s
    rw [hv s, hw s, map_sum, sum_inner]
    simp only [map_smul, inner_sum, inner_smul_left, inner_smul_right]
  rw [heq]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro l hl
  exact (hd l).mul ((Complex.continuous_conj.measurable.comp (hc i)).mul (hT (j i) (k l)))

theorem variableGramSchmidtNormed_matrix_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ i j, Measurable (fun s => inner ℂ (f s i) (T s (f s j)))) (i j : ℕ) :
    Measurable (fun s => inner ℂ (gramSchmidtNormed ℂ (f s) i)
      (T s (gramSchmidtNormed ℂ (f s) j))) :=
  (variableGramSchmidtNormed_finiteBorelSection f hgram i).operator_inner_measurable T hT
    (variableGramSchmidtNormed_finiteBorelSection f hgram j)

set_option maxHeartbeats 800000 in
theorem variableSelectedGramSchmidt_matrix_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite)
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ i j, Measurable (fun s => inner ℂ (f s i) (T s (f s j)))) (i j : ℕ) :
    Measurable (fun s => inner ℂ (variableSelectedGramSchmidt f s i)
      (T s (variableSelectedGramSchmidt f s j))) := by
  classical
  have hI (n : ℕ) : Measurable (fun s => Nat.nth (fun k => gramSchmidtNormed ℂ (f s) k ≠ 0) n) :=
    measurable_nat_nth _ (variableGramSchmidtNormed_nonzero_measurableSet f hgram) hinf n
  have hm : Measurable (fun p : S × (ℕ × ℕ) =>
      inner ℂ (gramSchmidtNormed ℂ (f p.1) p.2.1)
        (T p.1 (gramSchmidtNormed ℂ (f p.1) p.2.2))) :=
    measurable_from_prod_countable_left (fun ij =>
      variableGramSchmidtNormed_matrix_measurable f hgram T hT ij.1 ij.2)
  exact hm.comp (measurable_id.prodMk ((hI i).prodMk (hI j)))

end MeasureUnitary

end Source13

/- Preserved source skeleton: MeasureCantorContinuousBorel -/
section Source14
/-! Every continuous circle-valued Cantor multiplier has an actual Borel
realization on the one canonical Hilbert space, with the same explicit
Gram–Schmidt coordinates as the cylinder multipliers. -/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace OperatorCoding

namespace MeasureUnitary

noncomputable section

local instance _root_.MeasureUnitary.instMeasurableSpaceSubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCantorContinuousBorel : MeasurableSpace CanonicalHilbert := borel _
local instance _root_.MeasureUnitary.instBorelSpaceSubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCantorContinuousBorel : BorelSpace CanonicalHilbert := ⟨rfl⟩

def cantorProbabilityKernel : Kernel (ProbabilityMeasure CantorSpace) CantorSpace where
  toFun μ := (μ : Measure CantorSpace)
  measurable' := measurable_subtype_coe

theorem measurable_continuousMultiplierFundamental_inner (c : C(CantorSpace, ℂ))
    (k l : CantorFundamentalIndex) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalVector (μ : Measure CantorSpace) k)
        (continuousMultiplierL2 (μ : Measure CantorSpace) c
          (cantorFundamentalVector (μ : Measure CantorSpace) l))) := by
  let a : CantorSpace → CanonicalHilbert := (cantorCylinder k.1).indicator
    (fun _ => (lp.single 2 k.2 (1 : ℂ) : CanonicalHilbert))
  let b : CantorSpace → CanonicalHilbert := (cantorCylinder l.1).indicator
    (fun _ => (lp.single 2 l.2 (1 : ℂ) : CanonicalHilbert))
  have ha : Measurable a := measurable_const.indicator (cantorCylinder_measurable k.1)
  have hb : Measurable b := measurable_const.indicator (cantorCylinder_measurable l.1)
  have hm : StronglyMeasurable (fun x => inner ℂ (a x) (c x • b x)) :=
    (ha.inner (c.continuous.measurable.smul hb)).stronglyMeasurable
  have heq : (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalVector (μ : Measure CantorSpace) k)
        (continuousMultiplierL2 (μ : Measure CantorSpace) c
          (cantorFundamentalVector (μ : Measure CantorSpace) l))) =
      fun μ : ProbabilityMeasure CantorSpace => ∫ x, inner ℂ (a x) (c x • b x) ∂(μ : Measure CantorSpace) := by
    funext μ
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [continuousMultiplierL2_coe (μ : Measure CantorSpace) c
        (cantorFundamentalVector (μ : Measure CantorSpace) l),
      indicatorConstLp_coeFn (p := 2) (hs := cantorCylinder_measurable k.1)
        (hμs := measure_ne_top (μ : Measure CantorSpace) _)
        (c := (lp.single 2 k.2 (1 : ℂ) : CanonicalHilbert)),
      indicatorConstLp_coeFn (p := 2) (hs := cantorCylinder_measurable l.1)
        (hμs := measure_ne_top (μ : Measure CantorSpace) _)
        (c := (lp.single 2 l.2 (1 : ℂ) : CanonicalHilbert))] with x hm hk hl
    simp only [cantorFundamentalVector] at hm ⊢
    rw [hm, hk, hl]
  rw [heq]
  exact (hm.integral_kernel (κ := cantorProbabilityKernel)).measurable

def cantorContinuousCodedUnitary (c : C(CantorSpace, ℂ)) (hc : ∀ x, ‖c x‖ = 1)
    (μ : ProbabilityMeasure CantorSpace) : StrongUnitary CanonicalHilbert :=
  (cantorFiberCoordinates (μ : Measure CantorSpace)).symm.trans
    ((phaseEquiv (μ : Measure CantorSpace) c c.continuous.measurable hc).trans
      (cantorFiberCoordinates (μ : Measure CantorSpace)))

theorem cantorContinuousCodedUnitary_coefficient (c : C(CantorSpace, ℂ)) (hc : ∀ x, ‖c x‖ = 1)
    (μ : ProbabilityMeasure CantorSpace) (i j : ℕ) :
    cantorContinuousCodedUnitary c hc μ (lp.single 2 j (1 : ℂ) : CanonicalHilbert) i =
      inner ℂ (cantorFiberBasis (μ : Measure CantorSpace) i)
        (phaseEquiv (μ : Measure CantorSpace) c c.continuous.measurable hc
          (cantorFiberBasis (μ : Measure CantorSpace) j)) := by
  change (cantorFiberBasis (μ : Measure CantorSpace)).repr
    (phaseEquiv (μ : Measure CantorSpace) c c.continuous.measurable hc
      ((cantorFiberBasis (μ : Measure CantorSpace)).repr.symm (lp.single 2 j (1 : ℂ)))) i = _
  rw [HilbertBasis.repr_symm_single, HilbertBasis.repr_apply_apply]

theorem measurable_cantorContinuousBasis_inner (c : C(CantorSpace, ℂ)) (hc : ∀ x, ‖c x‖ = 1)
    (i j : ℕ) : Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFiberBasis (μ : Measure CantorSpace) i)
        (phaseEquiv (μ : Measure CantorSpace) c c.continuous.measurable hc
          (cantorFiberBasis (μ : Measure CantorSpace) j))) := by
  simp only [cantorFiberBasis_apply, ← continuousMultiplierL2_phase _ c hc]
  exact variableSelectedGramSchmidt_matrix_measurable
    (fun μ : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (μ : Measure CantorSpace))
    measurable_cantorFundamentalSequence_inner
    (fun μ => cantorFundamentalSequence_nonzero_infinite (μ : Measure CantorSpace))
    (fun μ => (continuousMultiplierL2 (μ : Measure CantorSpace) c).toLinearMap)
    (fun m n => measurable_continuousMultiplierFundamental_inner c
      (cantorFundamentalEnumeration m) (cantorFundamentalEnumeration n)) i j

theorem cantorContinuousCodedUnitary_measurable (c : C(CantorSpace, ℂ)) (hc : ∀ x, ‖c x‖ = 1) :
    @Measurable (ProbabilityMeasure CantorSpace) (StrongUnitary CanonicalHilbert)
      inferInstance (borel _) (cantorContinuousCodedUnitary c hc) := by
  apply strongUnitary_measurable_of_evaluations
  apply strongUnitary_measurable_evaluations_of_basis
  intro j
  apply canonicalHilbert_coordinates_measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_iff.mpr
  intro i
  simpa only [Function.comp_apply, cantorContinuousCodedUnitary_coefficient] using
    measurable_cantorContinuousBasis_inner c hc i j

end

end MeasureUnitary

end Source14

/- Preserved source skeleton: OperatorCyclicRepresentation -/
section Source15
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





end General



end OperatorCoding

end Source15

/- Preserved source skeleton: SeparatingMultiplierIntertwining -/
section Source16
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
end Source16

/- Preserved source skeleton: MeasureCyclicReduction -/
section Source17
/-! The actual forward cyclic-representation reduction: one injective
circle coordinate, infinite amplification, and Borel canonical coordinates.
Reflection uses Stone–Weierstrass and the explicit cylinder-density proof. -/

open MeasureTheory Set OperatorCoding

namespace MeasureUnitary

noncomputable section

local instance _root_.MeasureUnitary.instMeasurableSpaceSubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCyclicReduction : MeasurableSpace CanonicalHilbert := borel _
local instance _root_.MeasureUnitary.instBorelSpaceSubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCyclicReduction : BorelSpace CanonicalHilbert := ⟨rfl⟩
local instance _root_.MeasureUnitary.instMeasurableSpaceStrongUnitarySubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCyclicReduction : MeasurableSpace (StrongUnitary CanonicalHilbert) := borel _
local instance _root_.MeasureUnitary.instBorelSpaceStrongUnitarySubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCyclicReduction : BorelSpace (StrongUnitary CanonicalHilbert) := ⟨rfl⟩

theorem cantorCylinderPhase_continuous (k : CantorCylinderIndex) : Continuous (cantorCylinderPhase k) := by
  classical
  let g : (∀ i : k.1, Bool) → ℂ := fun y => if y ∈ k.2 then 1 else -1
  have heq : cantorCylinderPhase k = fun x => g (fun i : k.1 => x i) := by
    funext x
    rfl
  rw [heq]
  have hp : Continuous (fun x : CantorSpace => fun i : k.1 => x (i : ℕ)) :=
    continuous_pi (fun i => continuous_apply (i : ℕ))
  exact (continuous_of_discreteTopology : Continuous g).comp hp

def cantorCylinderContinuousPhase (k : CantorCylinderIndex) : C(CantorSpace, ℂ) :=
  ⟨cantorCylinderPhase k, cantorCylinderPhase_continuous k⟩

theorem circle_intertwiner_implies_cylinder_intertwiner
    (μ ν : ProbabilityMeasure CantorSpace) (U : CantorFiber μ ≃ₗᵢ[ℂ] CantorFiber ν)
    (hU : ∀ f, U (phaseEquiv (μ : Measure CantorSpace) cantorCircleContinuousMap
        cantorCirclePhase_continuous.measurable cantorCirclePhase_norm f) =
      phaseEquiv (ν : Measure CantorSpace) cantorCircleContinuousMap
        cantorCirclePhase_continuous.measurable cantorCirclePhase_norm (U f)) :
    ∀ k f, U (vectorCantorMultiplier (μ : Measure CantorSpace) k f) =
      vectorCantorMultiplier (ν : Measure CantorSpace) k (U f) := by
  let φ : C(CantorSpace, ℂ) →⋆ₐ[ℂ] (CantorFiber ν →L[ℂ] CantorFiber ν) :=
    (U.conjStarAlgEquiv : (CantorFiber μ →L[ℂ] CantorFiber μ) →⋆ₐ[ℂ]
      (CantorFiber ν →L[ℂ] CantorFiber ν)).comp
        (continuousMultiplierStarAlgHom (E := CanonicalHilbert) (μ : Measure CantorSpace))
  let ψ : C(CantorSpace, ℂ) →⋆ₐ[ℂ] (CantorFiber ν →L[ℂ] CantorFiber ν) :=
    continuousMultiplierStarAlgHom (ν : Measure CantorSpace)
  have heq : φ = ψ := by
    apply MeasureEquivalenceRestrictedPhase.starAlgHom_eq_of_separating_family
      φ ψ (U.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp
        (continuousMultiplierL2 (μ : Measure CantorSpace)).continuous)
      (continuousMultiplierL2 (ν : Measure CantorSpace)).continuous
      (fun _ : Unit => cantorCircleContinuousMap)
    · intro x y hxy
      exact ⟨(), fun h => hxy (cantorCirclePhase_injective h)⟩
    · intro i
      apply ContinuousLinearMap.ext
      intro f
      change U (continuousMultiplierL2 (μ : Measure CantorSpace) cantorCircleContinuousMap (U.symm f)) =
        continuousMultiplierL2 (ν : Measure CantorSpace) cantorCircleContinuousMap f
      rw [continuousMultiplierL2_phase _ _ cantorCirclePhase_norm,
        continuousMultiplierL2_phase _ _ cantorCirclePhase_norm]
      simpa using hU (U.symm f)
  intro k f
  have h := congrArg (fun F : C(CantorSpace, ℂ) →⋆ₐ[ℂ] (CantorFiber ν →L[ℂ] CantorFiber ν) =>
    F (cantorCylinderContinuousPhase k) (U f)) heq
  change U (continuousMultiplierL2 (μ : Measure CantorSpace) (cantorCylinderContinuousPhase k)
    (U.symm (U f))) = continuousMultiplierL2 (ν : Measure CantorSpace)
      (cantorCylinderContinuousPhase k) (U f) at h
  rw [U.symm_apply_apply, continuousMultiplierL2_phase _ _ (cantorCylinderPhase_norm k),
    continuousMultiplierL2_phase _ _ (cantorCylinderPhase_norm k)] at h
  exact h

def measureCodedUnitary (μ : ProbabilityMeasure CantorSpace) : StrongUnitary CanonicalHilbert :=
  cantorContinuousCodedUnitary cantorCircleContinuousMap cantorCirclePhase_norm μ

theorem measureCodedUnitary_measurable : Measurable measureCodedUnitary :=
  cantorContinuousCodedUnitary_measurable cantorCircleContinuousMap cantorCirclePhase_norm

theorem measureCodedUnitary_apply (μ : ProbabilityMeasure CantorSpace) (x : CanonicalHilbert) :
    measureCodedUnitary μ x = cantorFiberCoordinates (μ : Measure CantorSpace)
      (phaseEquiv (μ : Measure CantorSpace) cantorCircleContinuousMap
        cantorCirclePhase_continuous.measurable cantorCirclePhase_norm
        ((cantorFiberCoordinates (μ : Measure CantorSpace)).symm x)) := rfl

theorem measureCodedUnitary_equivalent_iff (μ ν : ProbabilityMeasure CantorSpace) :
    ElementConjugate (measureCodedUnitary μ) (measureCodedUnitary ν) ↔ MeasureEquivalent μ ν := by
  constructor
  · rintro ⟨W, hW⟩
    apply (amplifiedCantorMultiplierEquivalent_iff (μ : Measure CantorSpace) (ν : Measure CantorSpace)).mp
    let U : CantorFiber μ ≃ₗᵢ[ℂ] CantorFiber ν :=
      (cantorFiberCoordinates (μ : Measure CantorSpace)).trans
        (W.trans (cantorFiberCoordinates (ν : Measure CantorSpace)).symm)
    refine ⟨U, circle_intertwiner_implies_cylinder_intertwiner μ ν U (fun f => ?_)⟩
    have heq := congrArg (fun V : StrongUnitary CanonicalHilbert =>
      V (W (cantorFiberCoordinates (μ : Measure CantorSpace) f))) hW
    change W (measureCodedUnitary μ (W.symm (W (cantorFiberCoordinates (μ : Measure CantorSpace) f)))) =
      measureCodedUnitary ν (W (cantorFiberCoordinates (μ : Measure CantorSpace) f)) at heq
    rw [W.symm_apply_apply, measureCodedUnitary_apply, measureCodedUnitary_apply,
      LinearIsometryEquiv.symm_apply_apply] at heq
    have hh := congrArg (cantorFiberCoordinates (ν : Measure CantorSpace)).symm heq
    simpa only [U, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply] using hh
  · intro h
    let U : CantorFiber μ ≃ₗᵢ[ℂ] CantorFiber ν :=
      rnWeightedEquiv (μ : Measure CantorSpace) (ν : Measure CantorSpace) h.1 h.2
    have hU (f : CantorFiber μ) := rnWeightedEquiv_intertwines_phase (μ : Measure CantorSpace)
      cantorCircleContinuousMap cantorCirclePhase_continuous.measurable cantorCirclePhase_norm
      (ν : Measure CantorSpace) h.1 h.2 f
    let W : StrongUnitary CanonicalHilbert :=
      (cantorFiberCoordinates (μ : Measure CantorSpace)).symm.trans
        (U.trans (cantorFiberCoordinates (ν : Measure CantorSpace)))
    have hW (x : CanonicalHilbert) : W (measureCodedUnitary μ x) = measureCodedUnitary ν (W x) := by
      simpa only [W, measureCodedUnitary_apply, LinearIsometryEquiv.trans_apply,
        LinearIsometryEquiv.symm_apply_apply] using congrArg (cantorFiberCoordinates (ν : Measure CantorSpace))
          (hU ((cantorFiberCoordinates (μ : Measure CantorSpace)).symm x))
    refine ⟨W, ?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    simpa using hW (W.symm x)



def measureCodedCyclicRepresentation (μ : ProbabilityMeasure CantorSpace) :
    UnitaryRepresentation (Multiplicative ℤ) := zpowersHom _ (measureCodedUnitary μ)

theorem measureEquivalence_borelReduce_cyclicRepresentations :
    BorelReducesWith (inferInstance : MeasurableSpace (ProbabilityMeasure CantorSpace))
      (unitaryRepresentationBorel (Multiplicative ℤ)) MeasureEquivalent UnitaryRepresentationEquivalent :=
  ⟨measureCodedCyclicRepresentation, continuous_zpowersHom.borel_measurable.comp measureCodedUnitary_measurable,
    fun μ ν => (measureCodedUnitary_equivalent_iff μ ν).symm.trans (cyclic_conjugate_iff _ _).symm⟩

end

end MeasureUnitary

end Source17

/- Preserved source skeleton: BenchmarkOperatorTransport -/
section Source18
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

theorem measure_borelReduces_cyclic_representations :
    BorelReducesWith inferInstance (representationBorel (Multiplicative ℤ))
      MeasureEquivalent RepresentationEquivalent := by
  exact OperatorCoding.borelReducesWith_trans
    MeasureUnitary.measureEquivalence_borelReduce_cyclicRepresentations
    (representations_borelBireducible (Multiplicative ℤ)).2











end BenchmarkComparisons

end
end Source18

theorem solution : _root_.BenchmarkComparisons.RepresentationComparisons := by
  have hfree := BenchmarkComparisons.free_representations_borelBireducible_operators
  refine ⟨⟨BenchmarkComparisons.cyclic_representations_borelReduces_measure,
    BenchmarkComparisons.measure_borelReduces_cyclic_representations⟩, ?_, hfree⟩
  constructor
  · rcases BenchmarkComparisons.theorem_1_5.1 with ⟨f, hfm, hf⟩
    rcases hfree.2 with ⟨g, hgm, hg⟩
    refine ⟨g ∘ f, hgm.comp hfm, ?_⟩
    intro x y
    exact (hf x y).trans (hg (f x) (f y))
  · intro h
    apply BenchmarkComparisons.theorem_1_5.2
    rcases hfree.2 with ⟨f, hfm, hf⟩
    rcases h with ⟨g, hgm, hg⟩
    refine ⟨g ∘ f, hgm.comp hfm, ?_⟩
    intro x y
    exact (hf x y).trans (hg (f x) (f y))

#print axioms solution
