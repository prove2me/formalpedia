-- Prove2me | solution 1 for MeasureEquivalenceDenseInvariance.ae_invariant_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:19:26.927348+00:00
-- url     : https://prove2.me/submissions/6b20eb2a-777b-46a0-aecd-dd40fc33c4cc

import Definitions.Def_BenchmarkOperator20261026_DensityMeasure
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_RestrictedRoots
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_ZeroSumDense
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Finsupp.Encodable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
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
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Theorems.Thm_MeasureEquivalenceDensity_squareMeasure_continuous
import Theorems.Thm_MeasureEquivalenceRestrictedRoots_finiteOrbit_continuous
import Theorems.Thm_MeasureEquivalenceRootContinuity_continuous_root_of_mem

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





















end Action

section Graph

variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]









end Graph

end MeasureEquivalenceRNGraph

end

-- Preserved source skeleton: RestrictedRoots
section
/-! Restricting a square-density measure is continuous in its L2 root.
This supports extension of measurable-set invariance from a dense subgroup. -/

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedRoots

open MeasureEquivalenceDensity MeasureEquivalenceHellinger

variable {Z : Type*} [MeasurableSpace Z] (M : Measure Z)
    [IsFiniteMeasure M] {s : Set Z} (hs : MeasurableSet s)



theorem cutRoot_coe (f : Lp ℝ 2 M) :
    cutRoot M hs f =ᵐ[M] s.indicator (fun z => f z) := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
    (indicatorConstLp ∞ hs (measure_ne_top M s) (1:ℝ)) f,
    indicatorConstLp_coeFn (p := ∞) (hs := hs) (hμs := measure_ne_top M s)
      (c := (1:ℝ))] with z hmul hind
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 2
    (indicatorConstLp ∞ hs (measure_ne_top M s) (1:ℝ)) f) z = _
  rw [hmul]
  change (indicatorConstLp ∞ hs (measure_ne_top M s) (1:ℝ)) z * f z = _
  rw [hind]
  by_cases hz : z ∈ s <;> simp [hz]

theorem squareMeasure_cutRoot (f : Lp ℝ 2 M) :
    (squareMeasure M (cutRoot M hs f) : Measure Z) =
      (squareMeasure M f : Measure Z).restrict s := by
  change M.withDensity (fun z => ENNReal.ofReal ((cutRoot M hs f) z ^ 2)) =
    (M.withDensity (fun z => ENNReal.ofReal (f z ^ 2))).restrict s
  have hfun : (fun z => ENNReal.ofReal ((cutRoot M hs f) z ^ 2)) =ᵐ[M]
      s.indicator (fun z => ENNReal.ofReal (f z ^ 2)) := by
    filter_upwards [cutRoot_coe M hs f] with z hz
    rw [hz]
    by_cases hzs : z ∈ s <;> simp [hzs]
  rw [withDensity_congr_ae hfun, withDensity_indicator hs, ← restrict_withDensity hs]



theorem restrictedSquareMeasure_continuous [TopologicalSpace Z] [BorelSpace Z] :
    Continuous (restrictedSquareMeasure M hs) :=
  (squareMeasure_continuous M).comp (cutRoot M hs).continuous

include hs in
omit [IsFiniteMeasure M] in
theorem ae_eq_of_restrict_eq {t : Set Z} (ht : MeasurableSet t)
    (h : M.restrict s = M.restrict t) : s =ᵐ[M] t := by
  have hs0 : M (s \ t) = 0 := by
    have he := congrArg (fun ν : Measure Z => ν (s \ t)) h
    simpa only [Measure.restrict_apply (hs.diff ht), Set.diff_inter_self,
      Set.inter_eq_left.mpr Set.diff_subset, measure_empty] using he
  have ht0 : M (t \ s) = 0 := by
    have he := congrArg (fun ν : Measure Z => ν (t \ s)) h.symm
    simpa only [Measure.restrict_apply (ht.diff hs), Set.diff_inter_self,
      Set.inter_eq_left.mpr Set.diff_subset, measure_empty] using he
  rw [Filter.eventuallyEq_set]
  have ha : ∀ᵐ z ∂M, z ∉ s \ t := by simpa only [ae_iff, not_not] using hs0
  have hb : ∀ᵐ z ∂M, z ∉ t \ s := by simpa only [ae_iff, not_not] using ht0
  filter_upwards [ha, hb] with z haz hbz
  simp only [Set.mem_diff, not_and] at haz hbz
  constructor <;> intro hz
  · by_contra hzt
    exact haz hz hzt
  · by_contra hzs
    exact hbz hz hzs

include hs in
omit [IsFiniteMeasure M] in
theorem invariant_iff_restrict_map (e : Z ≃ᵐ Z) :
    (e ⁻¹' s) =ᵐ[M] s ↔ (M.map e).restrict s = (M.restrict s).map e := by
  rw [e.restrict_map]
  constructor
  · intro h
    exact congrArg (Measure.map e) (Measure.restrict_congr_set h)
  · intro h
    exact ae_eq_of_restrict_eq M (hs.preimage e.measurable) hs
      (e.measurableEmbedding.map_injective h)

section Action

variable {K : Type*} [Group K] [TopologicalSpace K] [FirstCountableTopology K]
    [TopologicalSpace Z] [BorelSpace Z] [MulAction K Z] [ContinuousSMul K Z]





end Action

end MeasureEquivalenceRestrictedRoots

end

/-! Measurable invariant sets persist under the intrinsic Polish group closure.
The proof uses actual restricted measures and the continuity of RN roots;
it does not assume continuity of a Koopman representation. -/
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
open MeasureEquivalenceDenseInvariance
open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceRootContinuity
open MeasureEquivalenceRestrictedRoots
variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

theorem solution (i : G →* A) (hi : Continuous i)
    (hmem : ∀ g, i g ∈ quasiInvariantSubgroup (K := A) M)
    (D : Set G) (hD : Dense D) (s : Set Z) (hs : MeasurableSet s)
    (hinv : ∀ d ∈ D, (fun z => i d • z) ⁻¹' s =ᵐ[M] s) :
    ∀ g : G, (fun z => i g • z) ⁻¹' s =ᵐ[M] s := by
  let F : G → FiniteMeasure Z := fun g =>
    restrictedSquareMeasure M hs (root (orbit M (i g) : Measure Z) M)
  let T : G → FiniteMeasure Z := fun g => finiteOrbit (M.restrict s) (i g)
  have hF : Continuous F :=
    (restrictedSquareMeasure_continuous M hs).comp (continuous_root_of_mem M i hi hmem)
  have hT : Continuous T := (finiteOrbit_continuous (M.restrict s)).comp hi
  have hF_value (g : G) :
      (F g : Measure Z) = (M.map (fun z => i g • z)).restrict s := by
    dsimp only [F, restrictedSquareMeasure]
    rw [squareMeasure_cutRoot]
    exact congrArg (fun ν : Measure Z => ν.restrict s)
      (squareMeasure_root M (orbit M (i g) : Measure Z) (hmem g).1)
  have hEq : F = T := by
    apply Continuous.ext_on hD hF hT
    intro d hd
    apply Subtype.ext
    exact (hF_value d).trans
      ((invariant_iff_restrict_map M hs (MeasurableEquiv.smul (i d))).mp (hinv d hd))
  intro g
  apply (invariant_iff_restrict_map M hs (MeasurableEquiv.smul (i g))).mpr
  exact (hF_value g).symm.trans
    (congrArg (fun ν : FiniteMeasure Z => (ν : Measure Z)) (congrFun hEq g))
