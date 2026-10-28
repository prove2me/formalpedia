-- Prove2me | solution 1 for MeasureEquivalenceRNGraph.isClosed_graph
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:17:00.451247+00:00
-- url     : https://prove2.me/submissions/a7d2437b-c6bf-453f-8847-327880c6d42f

import Definitions.Def_BenchmarkOperator20261026_DensityMeasure
import Definitions.Def_BenchmarkOperator20261026_DensitySquare
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Definitions.Def_BenchmarkOperator20261026_RNGraph
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
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Theorems.Thm_MeasureEquivalenceDensityGraph_isClosed_density_graph
import Theorems.Thm_MeasureEquivalenceDensity_squareMeasure_continuous
import Theorems.Thm_MeasureEquivalenceDensity_squareMeasure_injective_nonnegative
import Theorems.Thm_MeasureEquivalenceHellinger_root_dist_inverse

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

-- Preserved source skeleton: DensityMeasure
section
/-! Concrete finite measures with an L2 square density. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceDensity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)





theorem squareMeasure_ac (f : Lp ℝ 2 μ) :
    (squareMeasure μ f : Measure α) ≪ μ :=
  withDensity_absolutelyContinuous _ _







end MeasureEquivalenceDensity

end

-- Preserved source skeleton: RNGraph
section
open MeasureTheory Filter Set
open scoped Topology

namespace MeasureEquivalenceRNGraph

open MeasureEquivalenceDensity MeasureEquivalenceHellinger

variable {Z : Type*} [MeasurableSpace Z]

theorem squareMeasure_root (M ν : Measure Z) [SigmaFinite M] [IsFiniteMeasure ν]
    (hν : ν ≪ M) : (squareMeasure M (root ν M) : Measure Z) = ν := by
  change M.withDensity (fun x => ENNReal.ofReal ((root ν M) x ^ 2)) = ν
  calc
    _ = M.withDensity (ν.rnDeriv M) := by
      apply withDensity_congr_ae
      filter_upwards [root_coe ν M, Measure.rnDeriv_ne_top ν M] with x hx htop
      rw [hx, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop]
    _ = ν := Measure.withDensity_rnDeriv_eq ν M hν

section Action

variable {K : Type*} [CommGroup K] [TopologicalSpace K]
    [TopologicalSpace Z] [BorelSpace Z] [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]





theorem orbit_continuous [FirstCountableTopology K] : Continuous (orbit (K := K) M) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hrep : (fun g : K => ∫ z, f z ∂(orbit M g : Measure Z)) =
      fun g : K => ∫ z, f (g • z) ∂M := by
    funext g
    exact integral_map_equiv (MeasurableEquiv.smul g) f
  rw [hrep]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro g
    exact (f.continuous.comp (continuous_const_smul g)).aestronglyMeasurable
  · intro g
    exact Filter.Eventually.of_forall (fun z => f.norm_coe_le_norm (g • z))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun z => f.continuous.comp (continuous_id.smul continuous_const))









theorem feature_factor (h : quasiInvariantSubgroup (K := K) M) :
    squareMeasure M (feature M h : Lp ℝ 2 M) = orbit M (h : K) := by
  apply Subtype.ext
  exact squareMeasure_root M _ h.property.1

theorem feature_inverse (h k : quasiInvariantSubgroup (K := K) M) :
    dist (feature M h⁻¹) (feature M k⁻¹) = dist (feature M h) (feature M k) := by
  apply root_dist_inverse (MeasurableEquiv.smul (h : K)) (MeasurableEquiv.smul (k : K)) M
  · intro z
    exact smul_comm (h : K) (k : K) z
  · exact h.property.1
  · exact k.property.1
  · exact h.property.2
  · exact k.property.2



end Action

section Graph

variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]









end Graph

end MeasureEquivalenceRNGraph

end

open MeasureTheory Filter Set
open scoped Topology
namespace MeasureEquivalenceRNGraph
end MeasureEquivalenceRNGraph
open MeasureEquivalenceRNGraph
open MeasureEquivalenceDensity MeasureEquivalenceHellinger
variable {Z : Type*} [MeasurableSpace Z]
variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]

theorem solution : IsClosed (Set.range (graphMap (K := K) M)) := by
  let : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  apply MeasureEquivalenceDensityGraph.isClosed_density_graph
    (quasiInvariantSubgroup M) (feature M) (orbit M)
    (fun v : positiveUnitSphere M => squareMeasure M v)
    (fun ν : FiniteMeasure Z => (ν : Measure Z) ≪ M)
  · exact orbit_continuous M
  · exact (squareMeasure_continuous M).comp continuous_subtype_val
  · intro v w hvw
    apply Subtype.ext
    exact squareMeasure_injective_nonnegative M v.property.1 w.property.1 hvw
  · exact feature_factor M
  · intro v
    exact squareMeasure_ac M v
  · intro g
    rfl
  · exact feature_inverse M
