-- Prove2me | Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
-- name    : BenchmarkOperator20261026_SolenoidGroups
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:29:03.804946+00:00
-- url     : https://prove2.me/theorems/e1124f11-58f8-4154-a4b8-df2d593861a3
-- title:
--   Solenoid Groups
-- statement:
--   Defines the compact solenoid and its sequence product, the real and $\ell_1$ embeddings, the summable and zero-sum subgroups, coordinate shifts and two-point shifts. It also retains the structure instances and basic embedding and closed-subspace facts required by these constructions. These are the concrete parameter groups of the obstruction.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization SolenoidGroups.lean, lines 18–243; source SHA-256 0bcadf3f743451d7a036309ee98d74023f5458abd0cf627381724ed06077331d. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Polish

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

/-! The compact solenoid group and its real-sequence embedding from Section 8.
This file contains supporting lemmas, not the operator separation theorem. -/

open Filter Topology TopologicalSpace
open scoped Topology ENNReal

namespace MeasureEquivalenceSolenoid

noncomputable section

def characterGroup : AddSubgroup (ℚ → UnitAddCircle) where
  carrier := {f | f 0 = 0 ∧ ∀ q r, f (q+r) = f q + f r}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · simp [hf.1, hg.1]
    · intro q r
      simp only [Pi.add_apply, hf.2, hg.2]
      abel
  neg_mem' := by
    intro f hf
    constructor
    · simp [hf.1]
    · intro q r
      simp [hf.2, add_comm]

theorem characterGroup_closed : IsClosed (characterGroup : Set (ℚ → UnitAddCircle)) := by
  change IsClosed {f : ℚ → UnitAddCircle | f 0 = 0 ∧ ∀ q r, f (q+r) = f q + f r}
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    (isClosed_iInter fun q => isClosed_iInter fun r =>
      isClosed_eq (continuous_apply (q+r)) ((continuous_apply q).add (continuous_apply r)))

abbrev Solenoid := characterGroup
abbrev CompactSequences := ℕ → Solenoid

instance _root_.MeasureEquivalenceSolenoid.instCompactSpaceSubtypeForallRatUnitAddCircleMemAddSubgroupSolenoid : CompactSpace Solenoid :=
  characterGroup_closed.isClosedEmbedding_subtypeVal.compactSpace
instance _root_.MeasureEquivalenceSolenoid.instPolishSpaceSubtypeForallRatUnitAddCircleMemAddSubgroupSolenoid : PolishSpace Solenoid := characterGroup_closed.polishSpace
instance _root_.MeasureEquivalenceSolenoid.instMeasurableSpaceSubtypeForallRatUnitAddCircleMemAddSubgroupSolenoid : MeasurableSpace Solenoid := borel Solenoid
instance _root_.MeasureEquivalenceSolenoid.instBorelSpaceSubtypeForallRatUnitAddCircleMemAddSubgroupSolenoid : BorelSpace Solenoid := ⟨rfl⟩

def realCharacter (t : ℝ) : Solenoid :=
  ⟨fun q => ((q:ℝ)*t : ℝ), by
    constructor
    · simp
    · intro q r
      simp [add_mul]⟩

@[simp] theorem realCharacter_apply (t : ℝ) (q : ℚ) :
    (realCharacter t : ℚ → UnitAddCircle) q = ((q:ℝ)*t : ℝ) := rfl

theorem realCharacter_continuous : Continuous realCharacter := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro q
  exact (AddCircle.continuous_mk' (1:ℝ)).comp (continuous_const.mul continuous_id)



theorem realCharacter_injective : Function.Injective realCharacter := by
  intro x y hxy
  by_contra hne
  have hd : x-y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * |x-y|)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hnN : n ≠ 0 := by exact_mod_cast hn0.ne'
  let q : ℚ := 1 / n
  have hq : (q:ℝ) = 1/(n:ℝ) := by simp [q]
  have hc : ((((q:ℝ) * (x-y)):ℝ) : UnitAddCircle) = 0 := by
    have h := congrArg (fun f : Solenoid => (f:ℚ → UnitAddCircle) q) hxy
    simpa only [realCharacter_apply, mul_sub, AddCircle.coe_sub, sub_eq_zero] using h
  have habs : |(q:ℝ) * (x-y)| ≤ |(1:ℝ)| / 2 := by
    rw [hq, abs_mul, abs_one_div, abs_of_pos hn0, abs_one]
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hn0).mpr
    nlinarith [abs_nonneg (x-y)]
  have hh := (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) (by norm_num)).mpr habs
  rw [hc, norm_zero] at hh
  have hz : (q:ℝ) * (x-y) = 0 := abs_eq_zero.mp hh.symm
  rcases mul_eq_zero.mp hz with hq0 | hd0
  · rw [hq] at hq0
    exact one_div_ne_zero (by exact_mod_cast hnN) hq0
  · exact hd hd0

def sequenceEmbedding : (ℕ → ℝ) →+ CompactSequences where
  toFun x n := realCharacter (x n)
  map_zero' := by ext n q; simp [realCharacter]
  map_add' := by intro x y; ext n q; simp [realCharacter, mul_add]

theorem sequenceEmbedding_continuous : Continuous sequenceEmbedding := by
  apply continuous_pi
  intro n
  exact realCharacter_continuous.comp (continuous_apply n)

theorem sequenceEmbedding_injective : Function.Injective sequenceEmbedding := by
  intro x y h
  funext n
  exact realCharacter_injective (congrFun h n)




abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

def zeroSumSpace : Submodule ℝ RealL1 := (lp.tsumCLM ℝ ℕ ℝ).ker

@[simp] theorem mem_zeroSumSpace (h : RealL1) :
    h ∈ zeroSumSpace ↔ (∑' n, h n) = 0 := by
  rfl

theorem zeroSumSpace_closed : IsClosed (zeroSumSpace : Set RealL1) :=
  (lp.tsumCLM ℝ ℕ ℝ).isClosed_ker

instance _root_.MeasureEquivalenceSolenoid.instCompleteSpaceSubtypePreLpNatRealMemAddSubgroupRealL1SubmoduleZeroSumSpace : CompleteSpace zeroSumSpace :=
  zeroSumSpace_closed.isComplete.completeSpace_coe

def l1Embedding : RealL1 →+ CompactSequences where
  toFun h := sequenceEmbedding (h : ℕ → ℝ)
  map_zero' := map_zero sequenceEmbedding
  map_add' := by intro h k; exact map_add sequenceEmbedding (h:ℕ→ℝ) (k:ℕ→ℝ)



theorem l1Embedding_injective : Function.Injective l1Embedding := by
  intro x y h
  apply lp.ext
  exact sequenceEmbedding_injective h

def summableSubgroup : AddSubgroup CompactSequences := l1Embedding.range
def zeroSumSubgroup : AddSubgroup CompactSequences :=
  zeroSumSpace.toAddSubgroup.map l1Embedding



@[simp] theorem l1Embedding_mem_zeroSumSubgroup (h : RealL1) :
    l1Embedding h ∈ zeroSumSubgroup ↔ (∑' n, h n) = 0 := by
  constructor
  · rintro ⟨u, hu, he⟩
    have : u = h := l1Embedding_injective he
    simpa [this] using hu
  · intro hh
    exact ⟨h, (mem_zeroSumSpace h).mpr hh, rfl⟩

def coordinateShift (a : ℝ) : CompactSequences := l1Embedding (lp.single 1 0 a)



@[simp] theorem coordinateShift_mem_zeroSum (a : ℝ) :
    coordinateShift a ∈ zeroSumSubgroup ↔ a = 0 := by
  rw [coordinateShift, l1Embedding_mem_zeroSumSubgroup]
  simp



def twoPoint (a : ℝ) (n : ℕ) : RealL1 :=
  lp.single 1 0 a - lp.single 1 (n+1) a









def finiteTruncation (s : Finset ℕ) (x : ℕ → ℝ) : RealL1 :=
  ∑ i ∈ s, lp.single 1 i (x i)

theorem finiteTruncation_continuous (s : Finset ℕ) : Continuous (finiteTruncation s) := by
  apply continuous_finsetSum
  intro i _hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℝ) 1 i).continuous.comp
    (continuous_apply i)

theorem realL1_separable : SeparableSpace RealL1 := by
  have hd : Dense (⋃ s : Finset ℕ, Set.range (finiteTruncation s)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (1:ℝ≥0∞) ≠ ⊤) x)
    exact Filter.Eventually.of_forall (fun s => Set.mem_iUnion.mpr ⟨s, ⟨(x:ℕ→ℝ), rfl⟩⟩)
  apply hd.isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (finiteTruncation_continuous s))

instance _root_.MeasureEquivalenceSolenoid.instPolishSpaceSubtypePreLpNatRealMemAddSubgroupRealL1 : PolishSpace RealL1 := by
  letI := realL1_separable
  infer_instance

instance _root_.MeasureEquivalenceSolenoid.instPolishSpaceSubtypePreLpNatRealMemAddSubgroupRealL1SubmoduleZeroSumSpace : PolishSpace zeroSumSpace := zeroSumSpace_closed.polishSpace













end
end MeasureEquivalenceSolenoid


