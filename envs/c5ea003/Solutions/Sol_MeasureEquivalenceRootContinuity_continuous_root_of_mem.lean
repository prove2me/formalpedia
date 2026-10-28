-- Prove2me | solution 1 for MeasureEquivalenceRootContinuity.continuous_root_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:18:13.845634+00:00
-- url     : https://prove2.me/submissions/4b569fd7-3358-4145-abc5-9dc81a20fe8d

import Definitions.Def_BenchmarkOperator20261026_DensitySquare
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Theorems.Thm_MeasureEquivalenceInvariantGraph_graphGroup_topologicalGroup
import Theorems.Thm_MeasureEquivalenceRNGraph_isClosed_graph
import Theorems.Thm_MeasureEquivalenceTopology_continuous_borel_hom

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

-- Preserved source skeleton: DensitySquare
section
/-! The concrete L2-to-L1 density-square estimate used in the written proof.
This does not define a Hellinger distance or a topology on probability measures.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceDensity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)















theorem positiveUnitSphere_closed : IsClosed (positiveUnitSphere μ) := by
  change IsClosed ({f : Lp ℝ 2 μ | 0 ≤ f} ∩ {f : Lp ℝ 2 μ | ‖f‖ = 1})
  exact (isClosed_le continuous_const continuous_id).inter
    (isClosed_eq continuous_norm continuous_const)

theorem positiveUnitSphere_complete : CompleteSpace (positiveUnitSphere μ) :=
  (positiveUnitSphere_closed μ).isComplete.completeSpace_coe

end MeasureEquivalenceDensity

end

-- Preserved source skeleton: HellingerTransport
section
open MeasureTheory Filter

namespace MeasureEquivalenceHellinger

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]





theorem energy_map (e : α ≃ᵐ β) (μ ν ρ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] :
    energy (μ.map e) (ν.map e) (ρ.map e) = energy μ ν ρ := by
  unfold energy
  rw [integral_map_equiv]
  apply integral_congr_ae
  filter_upwards [e.measurableEmbedding.rnDeriv_map μ ρ,
    e.measurableEmbedding.rnDeriv_map ν ρ] with x hμ hν
  rw [hμ, hν]

theorem energy_change_reference (μ ν ρ σ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ ≪ σ) :
    energy μ ν σ = energy μ ν ρ := by
  unfold energy
  rw [← integral_toReal_rnDeriv_mul hρ]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := σ) hμ,
    Measure.rnDeriv_mul_rnDeriv (κ := σ) hν] with x hmx hnx
  simp only [Pi.mul_apply] at hmx hnx
  rw [← hmx, ← hnx, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.sqrt_mul (ENNReal.toReal_nonneg),
    Real.sqrt_mul (ENNReal.toReal_nonneg)]
  nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (ρ.rnDeriv σ x).toReal)]

theorem energy_fixed_reference_map (e : α ≃ᵐ α) (μ ν ρ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ.map e ≪ ρ) :
    energy (μ.map e) (ν.map e) ρ = energy μ ν ρ := by
  let : SigmaFinite (μ.map e) := e.measurableEmbedding.sigmaFinite_map
  let : SigmaFinite (ν.map e) := e.measurableEmbedding.sigmaFinite_map
  let : SigmaFinite (ρ.map e) := e.measurableEmbedding.sigmaFinite_map
  rw [energy_change_reference (μ.map e) (ν.map e) (ρ.map e) ρ
    (e.measurableEmbedding.absolutelyContinuous_map hμ)
    (e.measurableEmbedding.absolutelyContinuous_map hν) hρ]
  exact energy_map e μ ν ρ









theorem root_dist_sq (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    dist (root μ ρ) (root ν ρ) ^ 2 = energy μ ν ρ := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  unfold energy
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (root μ ρ) (root ν ρ), root_coe μ ρ,
    root_coe ν ρ] with x hs hμ hν
  simp only [Pi.sub_apply] at hs
  rw [hs, hμ, hν]
  simp [sq]

theorem root_dist_map (e : α ≃ᵐ α) (μ ν ρ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ.map e ≪ ρ) :
    dist (root (μ.map e) ρ) (root (ν.map e) ρ) = dist (root μ ρ) (root ν ρ) := by
  have he := energy_fixed_reference_map e μ ν ρ hμ hν hρ
  rw [← root_dist_sq, ← root_dist_sq] at he
  nlinarith [dist_nonneg (x := root (μ.map e) ρ) (y := root (ν.map e) ρ),
    dist_nonneg (x := root μ ρ) (y := root ν ρ)]









end MeasureEquivalenceHellinger

end

-- Preserved source skeleton: InvariantGraphGroup
section
open Set
open scoped Topology

namespace MeasureEquivalenceInvariantGraph

variable {K V : Type*} [CommGroup K] [MetricSpace K]
    [MetricSpace V] (H : Subgroup K) (r : H → V)















theorem graph_isometry : Isometry (graph H r) := Isometry.of_dist_eq (fun _ _ => rfl)

theorem inclusion_continuous : Continuous (inclusion H r) :=
  continuous_fst.comp (graph_isometry H r).continuous

theorem feature_continuous : Continuous (fun h : GraphGroup H r => r h) :=
  continuous_snd.comp (graph_isometry H r).continuous



variable (hleft : ∀ a h k : H, dist (r (a * h)) (r (a * k)) = dist (r h) (r k))







theorem graphGroup_complete [CompleteSpace K] [CompleteSpace V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h)))) :
    CompleteSpace (GraphGroup H r) := by
  let : CompleteSpace (Set.range (graph H r)) := hclosed.isComplete.completeSpace_coe
  exact (graph_isometry H r).isometryEquivOnRange.completeSpace

theorem graphGroup_secondCountable [SecondCountableTopology K] [SecondCountableTopology V] :
    SecondCountableTopology (GraphGroup H r) :=
  TopologicalSpace.secondCountableTopology_induced (GraphGroup H r) (K × V) (graph H r)

theorem graphGroup_polish [CompleteSpace K] [CompleteSpace V]
    [SecondCountableTopology K] [SecondCountableTopology V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h)))) :
    PolishSpace (GraphGroup H r) := by
  let : CompleteSpace (GraphGroup H r) := graphGroup_complete H r hclosed
  let : SecondCountableTopology (GraphGroup H r) := graphGroup_secondCountable H r
  infer_instance

section Presentation

variable [IsTopologicalGroup K] [CompleteSpace K] [CompleteSpace V]
    [SecondCountableTopology K] [SecondCountableTopology V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h))))
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]





end Presentation

end MeasureEquivalenceInvariantGraph

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



















theorem feature_mul_left (a h k : quasiInvariantSubgroup (K := K) M) :
    dist (feature M (a * h)) (feature M (a * k)) = dist (feature M h) (feature M k) := by
  have hd := root_dist_map (MeasurableEquiv.smul (a : K))
    (orbit M (h : K) : Measure Z) (orbit M (k : K) : Measure Z) M
    h.property.1 k.property.1 a.property.1
  change dist (root ((M.map (fun z => (h : K) • z)).map (fun z => (a : K) • z)) M)
    (root ((M.map (fun z => (k : K) • z)).map (fun z => (a : K) • z)) M) =
    dist (root (M.map (fun z => (h : K) • z)) M)
      (root (M.map (fun z => (k : K) • z)) M) at hd
  simp only [map_orbit] at hd
  exact hd

end Action

section Graph

variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]









end Graph

end MeasureEquivalenceRNGraph

end

/-! Actual Radon--Nikodym root continuity for the zero-sum l1 subgroup.
The general closed-graph argument is reused from the archived sequence-space
development. No continuity of densities is assumed. -/
open MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
open MeasureEquivalenceRootContinuity
open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceInvariantGraph
variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

theorem solution (i : G →* A) (hi : Continuous i)
    (hmem : ∀ g, i g ∈ quasiInvariantSubgroup (K := A) M) :
    Continuous (fun g => root (orbit M (i g) : Measure Z) M) := by
  letI : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let Q := GraphGroup (quasiInvariantSubgroup (K := A) M) (feature M)
  letI : IsTopologicalGroup Q := graphGroup_topologicalGroup _ _ (feature_mul_left M)
  letI : PolishSpace Q := graphGroup_polish _ _ (isClosed_graph M)
  letI : SecondCountableTopology Q := inferInstance
  letI : MeasurableSpace A := borel A
  letI : BorelSpace A := ⟨rfl⟩
  letI : MeasurableSpace Q := borel Q
  letI : BorelSpace Q := ⟨rfl⟩
  let j : G →* Q := i.codRestrict _ hmem
  have hj : Measurable j := by
    apply ((inclusion_continuous _ _).measurableEmbedding
      (inclusion_injective _ _)).measurable_comp_iff.mp
    exact hi.measurable
  have hc : Continuous j := MeasureEquivalenceTopology.continuous_borel_hom j hj
  exact continuous_subtype_val.comp ((feature_continuous _ _).comp hc)
