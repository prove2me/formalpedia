-- Prove2me | solution 1 for MeasureEquivalenceHellinger.upperSemicontinuous_integrated_affinity_standardBorel
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:31:31.582525+00:00
-- url     : https://prove2.me/submissions/636244a8-af90-4077-ab46-d17cc18bbc0c

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerOrbit
import Definitions.Def_BenchmarkOperator20261026_HellingerVariational
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_MeasureEquivalenceHellinger_affinity_compProd
import Theorems.Thm_MeasureEquivalenceHellinger_affinity_le_affinityTest_of_integrable
import Theorems.Thm_MeasureEquivalenceHellinger_exists_continuous_affinityTest_le
import Theorems.Thm_MeasureEquivalenceHellinger_exists_measurable_affinityTest_lt
import Theorems.Thm_MeasureEquivalenceRestrictedRoots_finiteOrbit_continuous

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

-- Preserved source skeleton: HellingerVariational
section
/-! Continuous positive test functions for Hellinger affinity. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceHellinger

























section Compact

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]













/-- Continuous strictly positive tests approximate affinity from above. -/
theorem exists_continuous_affinityTest_lt
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : ℝ) (hη : 0 < η) :
    ∃ g : C(Z, ℝ), (∀ z, 0 < g z) ∧ affinityTest μ ν g < affinity μ ν + η := by
  obtain ⟨f, c, C, hf, hc, hcC, hfb, hfsmall⟩ :=
    exists_measurable_affinityTest_lt μ ν (η / 2) (by positivity)
  obtain ⟨g, hgpos, hgsmall⟩ :=
    exists_continuous_affinityTest_le μ ν f hf c C hc hcC hfb (η / 2) (by positivity)
  exact ⟨g, hgpos, by linarith⟩

/-- Every continuous strictly positive test bounds affinity from above. -/
theorem affinity_le_continuous_affinityTest
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : C(Z, ℝ)) (hg : ∀ z, 0 < g z) : affinity μ ν ≤ affinityTest μ ν g := by
  apply affinity_le_affinityTest_of_integrable μ ν g hg
  · exact (BoundedContinuousFunction.mkOfCompact g).integrable μ
  · let ginv : C(Z, ℝ) := ⟨fun z => (g z)⁻¹,
      g.continuous.inv₀ (fun z => (hg z).ne')⟩
    exact (BoundedContinuousFunction.mkOfCompact ginv).integrable ν

/-- A variational characterization using continuous positive tests.
This strict-sublevel form also directly yields weak upper semicontinuity. -/
theorem affinity_lt_iff_exists_continuous_test
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ) :
    affinity μ ν < t ↔
      ∃ g : C(Z, ℝ), (∀ z, 0 < g z) ∧ affinityTest μ ν g < t := by
  constructor
  · intro h
    obtain ⟨g, hg, hsmall⟩ := exists_continuous_affinityTest_lt μ ν
      (t - affinity μ ν) (sub_pos.mpr h)
    exact ⟨g, hg, by linarith⟩
  · rintro ⟨g, hg, hsmall⟩
    exact (affinity_le_continuous_affinityTest μ ν g hg).trans_lt hsmall

/-- The functional of each fixed strictly positive continuous test is
jointly continuous for weak convergence of probabilities. -/
theorem continuous_affinityTest_probability
    (g : C(Z, ℝ)) (hg : ∀ z, 0 < g z) :
    Continuous (fun p : ProbabilityMeasure Z × ProbabilityMeasure Z =>
      affinityTest (p.1 : Measure Z) (p.2 : Measure Z) g) := by
  let ginv : C(Z, ℝ) := ⟨fun z => (g z)⁻¹,
    g.continuous.inv₀ (fun z => (hg z).ne')⟩
  exact ((ProbabilityMeasure.continuous_integral_continuousMap g).comp continuous_fst |>.add
    ((ProbabilityMeasure.continuous_integral_continuousMap ginv).comp continuous_snd)).div_const 2

/-- Hellinger affinity is jointly upper semicontinuous in the weak
topology of probabilities on a compact metric space. -/
theorem upperSemicontinuous_affinity_probability :
    UpperSemicontinuous (fun p : ProbabilityMeasure Z × ProbabilityMeasure Z =>
      affinity (p.1 : Measure Z) (p.2 : Measure Z)) := by
  intro p t ht
  obtain ⟨g, hg, hgt⟩ :=
    (affinity_lt_iff_exists_continuous_test (p.1 : Measure Z) (p.2 : Measure Z) t).mp ht
  have hcont := continuous_affinityTest_probability g hg
  filter_upwards [(hcont.tendsto p).eventually (gt_mem_nhds hgt)] with q hq
  exact (affinity_le_continuous_affinityTest (q.1 : Measure Z) (q.2 : Measure Z) g hg).trans_lt hq





end Compact

end MeasureEquivalenceHellinger

end

-- Preserved source skeleton: HellingerOrbit
section
/-! Upper semicontinuity of averaged component affinities, obtained by
applying the actual affinity theorem to an equal-marginal joint measure. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceHellinger

section Orbit

variable {K Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]



theorem probabilityOrbit_continuous : Continuous (probabilityOrbit (K := K) M) := by
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding Z).continuous_iff.mpr
  exact MeasureEquivalenceRestrictedRoots.finiteOrbit_continuous M

end Orbit



theorem rightCoordinateAction_continuous (K Y Z : Type*)
    [Monoid K] [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] :
    letI := rightCoordinateAction K Y Z
    ContinuousSMul K (Y × Z) := by
  letI := rightCoordinateAction K Y Z
  constructor
  change Continuous (fun p : K × (Y × Z) => (p.2.1, p.1 • p.2.2))
  exact (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.smul (continuous_snd.comp continuous_snd))

section Averaged

variable {K Y Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (η : Measure Y) [IsProbabilityMeasure η] (κ : Kernel Y Z) [IsMarkovKernel κ]

theorem upperSemicontinuous_integrated_affinity :
    UpperSemicontinuous (fun g : K =>
      ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η) := by
  letI := rightCoordinateAction K Y Z
  letI : ContinuousSMul K (Y × Z) := rightCoordinateAction_continuous K Y Z
  let J : Measure (Y × Z) := η ⊗ₘ κ
  letI : IsProbabilityMeasure J := inferInstance
  let P : ProbabilityMeasure (Y × Z) := ⟨J, inferInstance⟩
  have hc : Continuous (fun g : K => (P, probabilityOrbit J g)) :=
    continuous_const.prodMk (probabilityOrbit_continuous J)
  have hu := upperSemicontinuous_affinity_probability.comp hc
  have he (g : K) :
      affinity J (probabilityOrbit J g : Measure (Y × Z)) =
        ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η := by
    have hm : (probabilityOrbit J g : Measure (Y × Z)) =
        η ⊗ₘ κ.map (fun z => g • z) := by
      simpa only [probabilityOrbit, J, rightCoordinateAction, Prod.map_apply, id_eq] using
        (Measure.compProd_map (μ := η) (κ := κ) (measurable_const_smul g)).symm
    simp only [hm]
    exact (affinity_compProd η κ (κ.map (fun z => g • z))).trans
      (integral_congr_ae (Eventually.of_forall (fun y => by
        simp only [Kernel.map_apply _ (measurable_const_smul g)])))
  have hfun : (fun g : K => affinity J (probabilityOrbit J g : Measure (Y × Z))) =
      fun g : K => ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η := funext he
  change UpperSemicontinuous (fun g : K =>
    affinity J (probabilityOrbit J g : Measure (Y × Z))) at hu
  rw [hfun] at hu
  exact hu

end Averaged

section StandardBorelAverage

variable {K Y Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (η : Measure Y) [IsProbabilityMeasure η] (κ : Kernel Y Z) [IsMarkovKernel κ]



end StandardBorelAverage

end MeasureEquivalenceHellinger

end

/-! Upper semicontinuity of averaged component affinities, obtained by
applying the actual affinity theorem to an equal-marginal joint measure. -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger
variable {K Y Z : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (η : Measure Y) [IsProbabilityMeasure η] (κ : Kernel Y Z) [IsMarkovKernel κ]

theorem solution :
    UpperSemicontinuous (fun g : K =>
      ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η) := by
  let C := ℕ → Bool
  letI : MetricSpace C := TopologicalSpace.metrizableSpaceMetric C
  let e : Y → C := MeasurableSpace.mapNatBool Y
  have he : MeasurableEmbedding e :=
    (MeasurableSpace.measurable_mapNatBool Y).measurableEmbedding
      (MeasurableSpace.injective_mapNatBool Y)
  let r : C → Y := he.invFun
  have hr : Measurable r := he.measurable_invFun
  have hre : ∀ y, r (e y) = y := he.leftInverse_invFun
  let ηC : Measure C := η.map e
  letI : IsProbabilityMeasure ηC := η.isProbabilityMeasure_map he.measurable.aemeasurable
  let κC : Kernel C Z := κ.comap r hr
  have huc := upperSemicontinuous_integrated_affinity (K := K) ηC κC
  have hEq (g : K) :
      (∫ c, affinity (κC c) ((κC c).map (fun z => g • z)) ∂ηC) =
        ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η := by
    change (∫ c, affinity (κC c) ((κC c).map (fun z => g • z)) ∂η.map e) = _
    rw [he.integral_map]
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by simp only [κC, Kernel.comap_apply, hre])
  have hf : (fun g : K => ∫ c, affinity (κC c) ((κC c).map (fun z => g • z)) ∂ηC) =
      fun g : K => ∫ y, affinity (κ y) ((κ y).map (fun z => g • z)) ∂η := funext hEq
  rw [hf] at huc
  exact huc
