-- Prove2me | solution 1 for MeasureEquivalenceRigidity.zeroSum_not_reducible_to_measure_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:36:05.510796+00:00
-- url     : https://prove2.me/submissions/5e1fa647-edc9-40c9-b4d5-16acd7f2f4cb

import Definitions.Def_BenchmarkOperator20261026_CompactAveraging
import Definitions.Def_BenchmarkOperator20261026_HellingerInner
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_KernelEquivalence
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_ZeroSumConditional
import Definitions.Def_BenchmarkOperator20261026_ZeroSumDense
import Definitions.Def_BenchmarkOperator20261026_ZeroSumNonreduction
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_MeasureEquivalenceRigidity_coordinateShift_quasiInvariant

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

-- Preserved source skeleton: KernelEquivalence
section
/-!
Formal check of the conditional-measure step used in compact averaging.
This file does not claim to formalize the complete nonreducibility proof.
The equivalence relation here is literally mutual absolute continuity.
-/

open MeasureTheory ProbabilityTheory Filter

namespace MeasureEquivalenceResearch



theorem map_base_compProd
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) [IsFiniteMeasure mu]
    (kappa : Kernel X Y) [IsFiniteKernel kappa]
    (e : X ≃ᵐ X) (he : MeasurePreserving e mu mu) :
    (mu ⊗ₘ kappa).map (Prod.map e id) =
      mu ⊗ₘ kappa.comap e.symm e.symm.measurable := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (e.measurable.prodMap measurable_id) (hs.prod ht)]
  have hpre : (Prod.map e id) ⁻¹' (s ×ˢ t) = (e ⁻¹' s) ×ˢ t := by
    ext p
    rfl
  rw [hpre, Measure.compProd_apply_prod (e.measurable hs) ht,
    Measure.compProd_apply_prod hs ht]
  simpa only [Kernel.comap_apply, Function.comp_apply, e.symm_apply_apply] using
    he.setLIntegral_comp_preimage hs
      ((kappa.measurable_coe ht).comp e.symm.measurable)

theorem equivalent_compProd_iff
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (mu : Measure X) [SFinite mu] (kappa eta : Kernel X Y)
    [IsFiniteKernel kappa] [IsFiniteKernel eta] :
    EquivalentMeasures (mu ⊗ₘ kappa) (mu ⊗ₘ eta) ↔
      ∀ᵐ x ∂mu, EquivalentMeasures (kappa x) (eta x) := by
  unfold EquivalentMeasures
  rw [Measure.absolutelyContinuous_compProd_right_iff,
    Measure.absolutelyContinuous_compProd_right_iff]
  exact eventually_and.symm

theorem exact_kernel_cosets
    {G Y : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (mu : Measure G) [IsProbabilityMeasure mu]
    (H : AddSubgroup G) (kappa eta : Kernel G Y)
    [IsFiniteKernel kappa] [IsFiniteKernel eta]
    (g : G)
    (htranslate : ∀ x, eta x = kappa (x - g))
    (hreduction : ∀ x y, EquivalentMeasures (kappa x) (kappa y) ↔ x - y ∈ H) :
    EquivalentMeasures (mu ⊗ₘ eta) (mu ⊗ₘ kappa) ↔ g ∈ H := by
  rw [equivalent_compProd_iff]
  have hpoint : ∀ x, EquivalentMeasures (eta x) (kappa x) ↔ g ∈ H := by
    intro x
    rw [htranslate, hreduction]
    have hx : x - g - x = -g := by abel
    rw [hx, H.neg_mem_iff]
  simp_rw [hpoint]
  simp

theorem exact_quasi_invariance_of_kernel_reduction
    {G Y : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableAdd G]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (mu : Measure G) [IsProbabilityMeasure mu] [Measure.IsAddLeftInvariant mu]
    (H : AddSubgroup G) (kappa : Kernel G Y) [IsFiniteKernel kappa]
    (hreduction : ∀ x y, EquivalentMeasures (kappa x) (kappa y) ↔ x - y ∈ H)
    (g : G) :
    EquivalentMeasures ((mu ⊗ₘ kappa).map (fun p => (g + p.1, p.2)))
      (mu ⊗ₘ kappa) ↔ g ∈ H := by
  change EquivalentMeasures
    ((mu ⊗ₘ kappa).map (Prod.map (MeasurableEquiv.addLeft g) id))
    (mu ⊗ₘ kappa) ↔ g ∈ H
  rw [map_base_compProd mu kappa (MeasurableEquiv.addLeft g)
    (measurePreserving_add_left mu g)]
  apply exact_kernel_cosets mu H kappa _ g _ hreduction
  intro x
  simp [Kernel.comap_apply, sub_eq_add_neg, add_comm]






end MeasureEquivalenceResearch

end

-- Preserved source skeleton: CompactAveraging
section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceCompactAveraging

/-!
`ProbabilityMeasure Y` carries mathlib's canonical evaluation/Giry measurable
structure. A measurable probability-valued map therefore supplies an actual
Markov kernel without any extra kernel hypothesis. The Haar normalization,
joint probability, and exact translation quasi-invariance are constructed
below, including the concrete compact torus and a continuous action adapter.
-/

open MeasureEquivalenceResearch

section Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]













end Kernel

section CompactGroup

variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]







variable {G} {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]

theorem exact_quasi_invariance_of_probability_reduction
    (H : AddSubgroup G) (f : G → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H)
    (g : G) :
    EquivalentMeasures
      ((averagedMeasure (compactHaar G) f hf).map (fun z => (g + z.1, z.2)))
      (averagedMeasure (compactHaar G) f hf) ↔ g ∈ H := by
  exact exact_quasi_invariance_of_kernel_reduction (compactHaar G) H
    (probabilityKernel f hf) hred g

end CompactGroup

section Action



theorem continuous_baseTranslationAction (G Y : Type*)
    [AddMonoid G] [TopologicalSpace G] [ContinuousAdd G] [TopologicalSpace Y] :
    letI := baseTranslationAction G Y
    ContinuousSMul (Multiplicative G) (G × Y) := by
  let _ := baseTranslationAction G Y
  constructor
  change Continuous (fun z : Multiplicative G × (G × Y) =>
    (z.1.toAdd + z.2.1, z.2.2))
  exact ((continuous_toAdd.comp continuous_fst).add
    (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)

theorem exact_quasi_invariance_action
    {G Y : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (H : AddSubgroup G) (f : G → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H) :
    letI := baseTranslationAction G Y
    ∀ g : Multiplicative G,
      EquivalentMeasures ((averagedMeasure (compactHaar G) f hf).map (fun z => g • z))
        (averagedMeasure (compactHaar G) f hf) ↔ g.toAdd ∈ H := by
  intro g
  exact exact_quasi_invariance_of_probability_reduction H f hf hred g.toAdd

end Action



















end MeasureEquivalenceCompactAveraging

end

-- Preserved source skeleton: DensityGraphCompleteness
section
/-!
# Abstract density-graph completeness

This verifies the inverse-sequence / closed-graph argument with explicit
analytical interface hypotheses. It does not construct square-root RN densities
or verify those analytical interface hypotheses for L2 measures.
-/

open Filter Set
open scoped Topology

namespace MeasureEquivalenceDensityGraph

variable {K V P : Type*} [Group K] [MetricSpace K] [IsTopologicalGroup K]
  [MetricSpace V] [CompleteSpace V] [TopologicalSpace P] [T2Space P]







end MeasureEquivalenceDensityGraph

namespace MeasureEquivalenceInverseAC

open MeasureTheory

/-- The measure-specific inverse step: one-sided AC of the inverse translate
gives the opposite AC direction after pushing forward by the bijection. -/
theorem inverse_pushforward_ac {Z : Type*} [MeasurableSpace Z]
    (M : Measure Z) (T : Z ≃ᵐ Z) (h : M.map T.symm ≪ M) :
    M ≪ M.map T := by
  have hmap := T.measurableEmbedding.absolutelyContinuous_map h
  simpa only [MeasurableEquiv.map_map_symm] using hmap

/-- Mutual absolute continuity can therefore be tested using forward and
inverse one-sided absolute continuity. -/
theorem mutual_ac_iff_forward_inverse {Z : Type*} [MeasurableSpace Z]
    (M : Measure Z) (T : Z ≃ᵐ Z) :
    (M.map T ≪ M ∧ M ≪ M.map T) ↔
      (M.map T ≪ M ∧ M.map T.symm ≪ M) := by
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨hf, ?_⟩
    have hmap := T.symm.measurableEmbedding.absolutelyContinuous_map hb
    simpa only [MeasurableEquiv.map_symm_map] using hmap
  · rintro ⟨hf, hi⟩
    exact ⟨hf, inverse_pushforward_ac M T hi⟩

end MeasureEquivalenceInverseAC

end

-- Preserved source skeleton: RNGraph
section
open MeasureTheory Filter Set
open scoped Topology

namespace MeasureEquivalenceRNGraph

open MeasureEquivalenceDensity MeasureEquivalenceHellinger

variable {Z : Type*} [MeasurableSpace Z]



section Action

variable {K : Type*} [CommGroup K] [TopologicalSpace K]
    [TopologicalSpace Z] [BorelSpace Z] [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]











omit [IsProbabilityMeasure M] in
theorem mem_quasiInvariantSubgroup_iff (g : K) :
    g ∈ quasiInvariantSubgroup (K := K) M ↔
      M.map (fun z => g • z) ≪ M ∧ M ≪ M.map (fun z => g • z) := by
  exact (MeasureEquivalenceInverseAC.mutual_ac_iff_forward_inverse M
    (MeasurableEquiv.smul g)).symm









end Action

section Graph

variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]









end Graph

end MeasureEquivalenceRNGraph

end

-- Preserved source skeleton: ZeroSumNonreduction
section
/-! Compact Haar averaging turns a hypothetical reduction of the actual
zero-sum coset relation into a probability whose exact quasi-invariance
subgroup is that zero-sum subgroup. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRigidity

open MeasureEquivalenceCompactAveraging MeasureEquivalenceResearch
  MeasureEquivalenceSolenoid MeasureEquivalenceRNGraph



section Averaging

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated CompactSequences Y]

/-- The probability is constructed from normalized Haar measure and
the actual Markov kernel supplied by the proposed measurable reduction. -/
theorem zeroSum_probability_reduction_averaging
    (f : CompactSequences → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔
      x - y ∈ zeroSumSubgroup) :
    letI := baseTranslationAction CompactSequences Y
    letI : ContinuousSMul (Multiplicative CompactSequences) (CompactSequences × Y) :=
      continuous_baseTranslationAction CompactSequences Y
    ∃ M : Measure (CompactSequences × Y), IsProbabilityMeasure M ∧
      ∀ g : Multiplicative CompactSequences,
        g ∈ quasiInvariantSubgroup M ↔ g.toAdd ∈ zeroSumSubgroup := by
  letI := baseTranslationAction CompactSequences Y
  letI : ContinuousSMul (Multiplicative CompactSequences) (CompactSequences × Y) :=
    continuous_baseTranslationAction CompactSequences Y
  refine ⟨averagedMeasure (compactHaar CompactSequences) f hf, inferInstance, ?_⟩
  intro g
  rw [mem_quasiInvariantSubgroup_iff]
  exact exact_quasi_invariance_action zeroSumSubgroup f hf hred g

end Averaging









end MeasureEquivalenceRigidity

end

/-! Compact Haar averaging turns a hypothetical reduction of the actual
zero-sum coset relation into a probability whose exact quasi-invariance
subgroup is that zero-sum subgroup. -/
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
open MeasureEquivalenceCompactAveraging MeasureEquivalenceResearch
  MeasureEquivalenceSolenoid MeasureEquivalenceRNGraph

theorem solution :
    ¬ ∃ f : CompactSequences → ProbabilityMeasure CantorSample,
      Measurable f ∧ ∀ x y,
        EquivalentMeasures (f x : Measure CantorSample) (f y : Measure CantorSample) ↔
          x - y ∈ zeroSumSubgroup := by
  rintro ⟨f, hf, hred⟩
  letI : MetricSpace (CompactSequences × CantorSample) :=
    TopologicalSpace.metrizableSpaceMetric (CompactSequences × CantorSample)
  letI := baseTranslationAction CompactSequences CantorSample
  letI : ContinuousSMul (Multiplicative CompactSequences) (CompactSequences × CantorSample) :=
    continuous_baseTranslationAction CompactSequences CantorSample
  obtain ⟨M, hM, hexact⟩ := zeroSum_probability_reduction_averaging f hf hred
  letI : IsProbabilityMeasure M := hM
  have hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M :=
    fun h hh => (hexact (Multiplicative.ofAdd h)).mpr hh
  have h1 := coordinateShift_quasiInvariant M hQI 1
  have hH := (hexact (Multiplicative.ofAdd (coordinateShift 1))).mp h1
  have hz : (1 : ℝ) = 0 := (coordinateShift_mem_zeroSum 1).mp hH
  norm_num at hz
