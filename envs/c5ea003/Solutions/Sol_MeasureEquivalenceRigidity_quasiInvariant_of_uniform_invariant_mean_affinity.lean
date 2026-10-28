-- Prove2me | solution 1 for MeasureEquivalenceRigidity.quasiInvariant_of_uniform_invariant_mean_affinity
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:14:28.075454+00:00
-- url     : https://prove2.me/submissions/c4f2594f-d00d-4c2b-b6a3-36dc66ecc12a

import Definitions.Def_BenchmarkOperator20261026_ComponentQuasiInvariance
import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
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
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_invariantConditionalKernel_ergodic
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_invariantConditionalKernel_nonsingular
import Theorems.Thm_MeasureEquivalenceHellinger_affinity_eq_zero_iff_mutuallySingular
import Theorems.Thm_MeasureEquivalenceRigidity_absolutelyContinuous_or_mutuallySingular_of_ergodic
import Theorems.Thm_MeasureEquivalenceRigidity_ae_componentQI_of_uniform_mean_affinity

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

-- Preserved source skeleton: HellingerAffinity
section
/-!
Actual Hellinger affinity of finite measures via their L2 square-root RN
densities against their sum. This file proves the probability bounds and
the equivalence between zero affinity and mutual singularity.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Y : Type*} [MeasurableSpace Y]









theorem affinity_nonneg (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ affinity μ ν := by
  rw [affinity_integral]
  apply integral_nonneg
  intro y
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)









/-- A nonzero probability absolutely continuous with respect to another
probability has strictly positive Hellinger affinity. -/
theorem affinity_pos_of_absolutelyContinuous (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) : 0 < affinity μ ν := by
  apply lt_of_le_of_ne (affinity_nonneg μ ν)
  intro hzero
  have hsing := (affinity_eq_zero_iff_mutuallySingular μ ν).mp hzero.symm
  have hμzero := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hμν hsing
  have hm := congrArg (fun ρ : Measure Y => ρ Set.univ) hμzero
  simp at hm

end MeasureEquivalenceHellinger

end

-- Preserved source skeleton: NonsingularDichotomy
section
/-!
The equivalence-or-singularity dichotomy for ergodic nonsingular measures
of one countable group action. Ergodicity is stated explicitly for
measurable invariant sets; no invariance of the measures is assumed.
-/

open MeasureTheory MeasureTheory.Measure Set

namespace MeasureEquivalenceRigidity

variable {G Y : Type*} [Group G] [Countable G]
    [MeasurableSpace Y] [MulAction G Y]









/-- Two ergodic nonsingular measures for the same countable action
are equivalent or mutually singular. The ergodicity tests refer to
actual measurable invariant sets. The measures need not be invariant,
finite, or have the same Radon--Nikodym cocycle. -/
theorem equivalent_or_mutuallySingular_of_nonsingular_ergodic
    (μ ν : Measure Y)
    (hμns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) μ μ)
    (hνns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) ν ν)
    (hμerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (hνerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → ν s = 0 ∨ ν sᶜ = 0) :
    (μ ≪ ν ∧ ν ≪ μ) ∨ μ ⟂ₘ ν := by
  rcases absolutelyContinuous_or_mutuallySingular_of_ergodic μ ν hνns hμerg with h | h
  · rcases absolutelyContinuous_or_mutuallySingular_of_ergodic ν μ hμns hνerg with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr h'.symm
  · exact Or.inr h

end MeasureEquivalenceRigidity

end

-- Preserved source skeleton: HellingerErgodic
section
/-! The actual Hellinger zero test on nonsingular ergodic components. -/

open MeasureTheory MeasureTheory.Measure

namespace MeasureEquivalenceRigidity

open MeasureEquivalenceHellinger

variable {G Y : Type*} [Group G] [Countable G]
    [MeasurableSpace Y] [MulAction G Y]

/-- On ergodic nonsingular probability components, zero Hellinger
affinity means failure of measure equivalence. -/
theorem affinity_eq_zero_iff_not_equivalent_of_nonsingular_ergodic
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) μ μ)
    (hνns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) ν ν)
    (hμerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (hνerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → ν s = 0 ∨ ν sᶜ = 0) :
    affinity μ ν = 0 ↔ ¬ (μ ≪ ν ∧ ν ≪ μ) := by
  constructor
  · intro hzero heq
    exact (ne_of_gt (affinity_pos_of_absolutelyContinuous μ ν heq.1)) hzero
  · intro hneq
    rcases equivalent_or_mutuallySingular_of_nonsingular_ergodic
      μ ν hμns hνns hμerg hνerg with heq | hsing
    · exact False.elim (hneq heq)
    · exact (affinity_eq_zero_iff_mutuallySingular μ ν).mpr hsing

end MeasureEquivalenceRigidity

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

-- Preserved source skeleton: ComponentQuasiInvariance
section
/-! Actual quasi-invariance subgroups of component probabilities and
translation of nonsingular ergodic measures by commuting transformations. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set

namespace MeasureEquivalenceRigidity

open MeasureEquivalenceRNGraph MeasureEquivalenceHellinger

section Components

variable {K Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (κ : Kernel Y Z) [IsMarkovKernel κ]



theorem mem_componentQI_iff (g : K) (y : Y) :
    g ∈ componentQI κ y ↔
      (κ y).map (fun z => g • z) ≪ κ y ∧ κ y ≪ (κ y).map (fun z => g • z) :=
  mem_quasiInvariantSubgroup_iff (κ y) g



end Components

section Commuting

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    (μ : Measure Z) (e : Z ≃ᵐ Z)
    (hcomm : ∀ (g : G) (z : Z), e (g • z) = g • e z)

include hcomm in
theorem nonsingular_map_of_commute
    (hns : ∀ g : G, QuasiMeasurePreserving (fun z : Z => g • z) μ μ) :
    ∀ g : G, QuasiMeasurePreserving (fun z : Z => g • z) (μ.map e) (μ.map e) := by
  intro g
  refine ⟨(hns g).measurable, ?_⟩
  have heq : (μ.map e).map (fun z => g • z) = (μ.map (fun z => g • z)).map e := by
    rw [Measure.map_map (hns g).measurable e.measurable,
      Measure.map_map e.measurable (hns g).measurable]
    congr 1
    funext z
    exact (hcomm g z).symm
  rw [heq]
  exact (hns g).absolutelyContinuous.map e.measurable

include hcomm in
theorem ergodic_map_of_commute
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0) :
    ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z => g • z) ⁻¹' s = s) →
      (μ.map e) s = 0 ∨ (μ.map e) sᶜ = 0 := by
  intro s hs hinv
  have hi : ∀ g : G, (fun z => g • z) ⁻¹' (e ⁻¹' s) = e ⁻¹' s := by
    intro g
    ext z
    change e (g • z) ∈ s ↔ e z ∈ s
    rw [hcomm]
    exact Set.ext_iff.mp (hinv g) (e z)
  have h := herg (e ⁻¹' s) (hs.preimage e.measurable) hi
  simpa only [Measure.map_apply e.measurable hs,
    Measure.map_apply e.measurable hs.compl, Set.preimage_compl] using h

end Commuting

end MeasureEquivalenceRigidity

end

-- Preserved source skeleton: InvariantConditional
section
/-!
The exact invariant sigma-algebra and its actual conditional-probability
kernel. This module establishes invariance and reconstruction; it does
not assert ergodicity of the component probabilities.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace MeasureEquivalenceErgodicDecomposition



variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]















section Conditional

variable [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]









/-- Integrating the invariant conditional kernel reconstructs the
original finite measure. -/
theorem invariantConditionalKernel_comp :
    invariantConditionalKernel (G := G) μ ∘ₘ μ = μ := by
  ext s hs
  have hcomp := congrArg (fun ρ : Measure Z => ρ s)
    (condExpKernel_comp_trim (μ := μ) (invariantSigma_le (G := G)))
  dsimp only at hcomp
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)] at hcomp ⊢
  change (∫⁻ z, condExpKernel μ (invariantSigma (G := G)) z s ∂μ) = μ s
  rw [← lintegral_trim (invariantSigma_le (G := G)) (measurable_condExpKernel hs)]
  exact hcomp













/-- Countability gives one conull set on which every group element is
nonsingular for the same conditional probability. -/
theorem invariantConditionalKernel_nonsingular_all [Countable G]
    [MeasurableSpace.CountablyGenerated Z]
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ) :
    ∀ᵐ z ∂μ, ∀ g : G,
      Measure.QuasiMeasurePreserving (fun w : Z => g • w)
        (invariantConditionalKernel (G := G) μ z) (invariantConditionalKernel (G := G) μ z) := by
  have hall := ae_all_iff.mpr (fun g => invariantConditionalKernel_nonsingular μ g (hns g))
  filter_upwards [hall] with z hz
  intro g
  exact ⟨(hns g).measurable, hz g⟩



end Conditional

end MeasureEquivalenceErgodicDecomposition

end

-- Preserved source skeleton: ComponentRigidityRoots
section
/-! Actual component quasi-invariance is detected by Hellinger affinity,
and vanishing mean deficits along roots give component quasi-invariance. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceRigidity

open MeasureEquivalenceHellinger MeasureEquivalenceErgodicDecomposition

section Pointwise

variable {K G Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [Group G] [Countable G]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] [MulAction G Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (κ : Kernel Y Z) [IsMarkovKernel κ]

/-- The zero-affinity test uses actual nonsingularity and ergodicity of
the conditional probability and actual commutation of the translate. -/
theorem component_affinity_zero_iff
    (y : Y) (k : K)
    (hns : ∀ g : G, QuasiMeasurePreserving (fun z : Z => g • z) (κ y) (κ y))
    (herg : ∀ B : Set Z, MeasurableSet B →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' B = B) → (κ y) B = 0 ∨ (κ y) Bᶜ = 0)
    (hcomm : ∀ (g : G) (z : Z), k • (g • z) = g • (k • z)) :
    affinity (κ y) ((κ y).map (fun z => k • z)) = 0 ↔ k ∉ componentQI κ y := by
  let e : Z ≃ᵐ Z := MeasurableEquiv.smul k
  letI : IsProbabilityMeasure ((κ y).map e) :=
    (κ y).isProbabilityMeasure_map e.measurable.aemeasurable
  have hecomm : ∀ (g : G) (z : Z), e (g • z) = g • e z := hcomm
  have hA := affinity_eq_zero_iff_not_equivalent_of_nonsingular_ergodic
    (κ y) ((κ y).map e) hns
    (nonsingular_map_of_commute (κ y) e hecomm hns) herg
    (ergodic_map_of_commute (κ y) e hecomm herg)
  simpa only [mem_componentQI_iff, and_comm] using hA

end Pointwise

section ActualComponents

variable {K G Z : Type*} [CommGroup K] [TopologicalSpace K]
    [Group G] [Countable G]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] [MeasurableEq Z]
    [MulAction K Z] [ContinuousSMul K Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (hns : ∀ g : G, QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

include hns in
/-- One conull set of actual invariant conditional probabilities works
for every commuting translate. No uncountable intersection is taken. -/
theorem invariant_components_affinity_zero_iff :
    ∀ᵐ x ∂μ, ∀ k : K,
      (∀ (g : G) (z : Z), k • (g • z) = g • (k • z)) →
      (affinity (invariantConditionalKernel (G := G) μ x)
        ((invariantConditionalKernel (G := G) μ x).map (fun z => k • z)) = 0 ↔
          k ∉ componentQI (invariantConditionalKernel (G := G) μ) x) := by
  have hNS := invariantConditionalKernel_nonsingular_all μ hns
  have hErg := invariantConditionalKernel_ergodic μ hns
  filter_upwards [hNS, hErg] with x hxNS hxErg
  intro k hcomm
  exact component_affinity_zero_iff _ x k hxNS hxErg hcomm

end ActualComponents

section Roots



variable {K Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (η : Measure Y) [IsProbabilityMeasure η]
    (κ : Kernel Y Z) [IsMarkovKernel κ]





omit [IsProbabilityMeasure η] in
/-- Fiberwise equivalence passes through the actual barycenter. -/
theorem quasiInvariant_barycenter_of_ae_componentQI
    (k : K) (hQI : ∀ᵐ y ∂η, k ∈ componentQI κ y) :
    k ∈ MeasureEquivalenceRNGraph.quasiInvariantSubgroup (κ ∘ₘ η) := by
  rw [MeasureEquivalenceRNGraph.mem_quasiInvariantSubgroup_iff,
    Measure.map_comp η κ (measurable_const_smul k)]
  constructor
  · exact Measure.AbsolutelyContinuous.comp_left η (hQI.mono (fun y hy => by
      simpa only [Kernel.map_apply _ (measurable_const_smul k)] using
        (mem_componentQI_iff κ k y).mp hy |>.1))
  · exact Measure.AbsolutelyContinuous.comp_left η (hQI.mono (fun y hy => by
      simpa only [Kernel.map_apply _ (measurable_const_smul k)] using
        (mem_componentQI_iff κ k y).mp hy |>.2))

end Roots

section ActualRigidity

variable {K G Z : Type*} [CommGroup K] [TopologicalSpace K]
    [Group G] [Countable G]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] [MeasurableEq Z]
    [MulAction K Z] [ContinuousSMul K Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hns : ∀ d : G, QuasiMeasurePreserving (fun z : Z => d • z) μ μ)



end ActualRigidity

end MeasureEquivalenceRigidity

end

/-! Actual component quasi-invariance is detected by Hellinger affinity,
and vanishing mean deficits along roots give component quasi-invariance. -/
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
open MeasureEquivalenceHellinger MeasureEquivalenceErgodicDecomposition
variable {K G Z : Type*} [CommGroup K] [TopologicalSpace K]
    [Group G] [Countable G]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] [MeasurableEq Z]
    [MulAction K Z] [ContinuousSMul K Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hns : ∀ d : G, QuasiMeasurePreserving (fun z : Z => d • z) μ μ)

include hns

theorem solution
    (g : ℝ →+ Additive K)
    (hcomm : ∀ (k : K) (d : G) (z : Z), k • (d • z) = d • (k • z))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, |b| < δ → 1 - ε ≤ ∫ x,
        affinity (invariantConditionalKernel (G := G) μ x)
          ((invariantConditionalKernel (G := G) μ x).map
            (fun z => Additive.toMul (g b) • z)) ∂μ)
    (a : ℝ) :
    Additive.toMul (g a) ∈ MeasureEquivalenceRNGraph.quasiInvariantSubgroup μ := by
  have hzero : ∀ᵐ x ∂μ, ∀ k : K,
      affinity (invariantConditionalKernel (G := G) μ x)
        ((invariantConditionalKernel (G := G) μ x).map (fun z => k • z)) = 0 ↔
          k ∉ componentQI (invariantConditionalKernel (G := G) μ) x := by
    filter_upwards [invariant_components_affinity_zero_iff (K := K) μ hns] with x hx
    exact fun k => hx k (hcomm k)
  have hQI := ae_componentQI_of_uniform_mean_affinity μ
    (invariantConditionalKernel (G := G) μ) g hzero hsmall a
  have h := quasiInvariant_barycenter_of_ae_componentQI μ
    (invariantConditionalKernel (G := G) μ) (Additive.toMul (g a)) hQI
  rwa [invariantConditionalKernel_comp] at h
