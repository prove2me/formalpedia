-- Prove2me | solution 1 for MeasureEquivalenceRigidity.ae_componentQI_of_real_root_mean_affinity
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:08:14.771983+00:00
-- url     : https://prove2.me/submissions/063696b6-12c9-4f26-87fd-d571c3d8a3bc

import Definitions.Def_BenchmarkOperator20261026_ComponentQuasiInvariance
import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerKernel
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
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
import Theorems.Thm_MeasureEquivalenceRigidity_ae_mem_of_root_mean_affinity

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





theorem affinity_le_one (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : affinity μ ν ≤ 1 := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  calc
    affinity μ ν ≤ ‖root μ (μ + ν)‖ * ‖root ν (μ + ν)‖ := real_inner_le_norm _ _
    _ = 1 := by rw [root_probability_norm μ _ hμ, root_probability_norm ν _ hν, mul_one]





end MeasureEquivalenceHellinger

end

-- Preserved source skeleton: HellingerKernel
section
/-! Actual disintegration of Hellinger affinity for equal-marginal kernels. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η]







theorem kernelAffinityIntegrand_measurable : Measurable (kernelAffinityIntegrand κ η) :=
  (κ.measurable_rnDeriv (κ+η)).ennreal_toReal.sqrt.mul
    (η.measurable_rnDeriv (κ+η)).ennreal_toReal.sqrt

theorem affinity_kernel_fiber (x : X) :
    (∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) = affinity (κ x) (η x) := by
  rw [affinity_integral]
  apply integral_congr_ae
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x),
    η.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x)] with y hk he
  simp only [kernelAffinityIntegrand, hk, he]
  rfl

theorem kernelAffinity_measurable : Measurable (fun x => affinity (κ x) (η x)) := by
  have h := (kernelAffinityIntegrand_measurable κ η).stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ+η)
  have he : (fun x => ∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) =
      fun x => affinity (κ x) (η x) := funext (affinity_kernel_fiber κ η)
  rw [he] at h
  exact h.measurable



end MeasureEquivalenceHellinger

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

theorem measurableSet_componentQI (g : K) : MeasurableSet {y | g ∈ componentQI κ y} := by
  have ha := Kernel.measurableSet_absolutelyContinuous (κ.map (fun z => g • z)) κ
  have hb := Kernel.measurableSet_absolutelyContinuous κ (κ.map (fun z => g • z))
  have he : {y | g ∈ componentQI κ y} =
      {y | (κ.map (fun z => g • z)) y ≪ κ y} ∩
      {y | κ y ≪ (κ.map (fun z => g • z)) y} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_componentQI_iff,
      Kernel.map_apply _ (measurable_const_smul g)]
  rw [he]
  exact ha.inter hb

end Components

section Commuting

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    (μ : Measure Z) (e : Z ≃ᵐ Z)
    (hcomm : ∀ (g : G) (z : Z), e (g • z) = g • e z)





end Commuting

end MeasureEquivalenceRigidity

end

-- Preserved source skeleton: RigidityRoots
section
/-!
The countable-roots step in the manuscript's quasi-invariance rigidity argument.

This module is a helper for Theorems 1.3 and 1.4. It does not assert the
ergodic decomposition, affinity estimate, or representation construction.
The hypotheses below are precisely the quantitative component estimates
needed after those analytic steps have been established.
-/

open Filter MeasureTheory
open scoped Topology ENNReal

namespace MeasureEquivalenceRigidity

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}







variable {K : Type*} [AddCommGroup K]









/-- Concrete real-line form of the affinity roots argument. In the
manuscript `S y` is the quasi-invariance subgroup of the conditional
ergodic measure, and `A n y` is its affinity with its translate by the
`(n+1)`st root of `g a`. -/
theorem ae_mem_of_real_root_mean_affinity
    [IsProbabilityMeasure μ]
    (g : ℝ →+ K) (S : Y → AddSubgroup K) (a : ℝ)
    (A : ℕ → Y → ℝ)
    (hbad : ∀ n, MeasurableSet {y | g (a / ((n + 1 : ℕ) : ℝ)) ∉ S y})
    (hA : ∀ n, Measurable (A n))
    (hA_nonneg : ∀ n y, 0 ≤ A n y)
    (hA_le : ∀ n y, A n y ≤ 1)
    (hzero : ∀ n, ∀ᵐ y ∂μ, g (a / ((n + 1 : ℕ) : ℝ)) ∉ S y → A n y = 0)
    (ε : ℕ → ℝ)
    (hmean : ∀ n, 1 - ε n ≤ ∫ y, A n y ∂μ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂μ, g a ∈ S y := by
  apply ae_mem_of_root_mean_affinity S (g a)
    (fun n => g (a / ((n + 1 : ℕ) : ℝ))) (fun n => n + 1) _ A
    hbad hA hA_nonneg hA_le hzero ε hmean hε
  intro n
  rw [← map_nsmul, nsmul_eq_mul]
  congr 1
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel₀ a hn

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
variable {K Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (η : Measure Y) [IsProbabilityMeasure η]
    (κ : Kernel Y Z) [IsMarkovKernel κ]

theorem solution
    (g : ℝ →+ Additive K) (a : ℝ)
    (hzero : ∀ᵐ y ∂η, ∀ k : K,
      affinity (κ y) ((κ y).map (fun z => k • z)) = 0 ↔ k ∉ componentQI κ y)
    (ε : ℕ → ℝ)
    (hmean : ∀ n, 1 - ε n ≤ ∫ y,
      affinity (κ y) ((κ y).map (fun z => Additive.toMul (g (a / ((n+1 : ℕ) : ℝ))) • z)) ∂η)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂η, Additive.toMul (g a) ∈ componentQI κ y := by
  let S : Y → AddSubgroup (Additive K) := fun y => (componentQI κ y).toAddSubgroup
  let A : ℕ → Y → ℝ := fun n y => affinity (κ y)
    ((κ y).map (fun z => Additive.toMul (g (a / ((n+1 : ℕ) : ℝ))) • z))
  have hbad : ∀ n, MeasurableSet {y | g (a / ((n+1 : ℕ) : ℝ)) ∉ S y} := by
    intro n
    exact (measurableSet_componentQI κ _).compl
  have hAm : ∀ n, Measurable (A n) := by
    intro n
    simpa only [A, Kernel.map_apply _ (measurable_const_smul _)] using
      kernelAffinity_measurable κ
        (κ.map (fun z => Additive.toMul (g (a / ((n+1 : ℕ) : ℝ))) • z))
  have hAzero : ∀ n, ∀ᵐ y ∂η, g (a / ((n+1 : ℕ) : ℝ)) ∉ S y → A n y = 0 := by
    intro n
    filter_upwards [hzero] with y hy
    intro hnot
    exact (hy _).mpr hnot
  have hAle : ∀ n y, A n y ≤ 1 := by
    intro n y
    letI : IsProbabilityMeasure ((κ y).map
        (fun z => Additive.toMul (g (a / ((n+1 : ℕ) : ℝ))) • z)) :=
      (κ y).isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
    exact affinity_le_one _ _
  exact ae_mem_of_real_root_mean_affinity g S a A hbad hAm
    (fun n y => affinity_nonneg _ _) hAle hAzero ε hmean hε
