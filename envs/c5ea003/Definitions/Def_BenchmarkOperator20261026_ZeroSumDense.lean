-- Prove2me | Definitions.Def_BenchmarkOperator20261026_ZeroSumDense
-- name    : BenchmarkOperator20261026_ZeroSumDense
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:52:37.50038+00:00
-- url     : https://prove2.me/theorems/1b2c9da2-2b5a-48f6-b961-33ec428c773a
-- title:
--   Zero Sum Dense
-- statement:
--   Defines the zero-total projection on $\ell_1$, finitely supported rational vectors, their zero-sum projection and the resulting countable subgroup. The retained countability and single-coordinate identity justify these constructions. Later theorems use the subgroup as dense rational data.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization ZeroSumDense.lean, lines 15–82; source SHA-256 d72675ffb6bdcc27e6d2a28465564ed378b5728467709a67f040d6d91b87695c. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Finsupp.Encodable
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
import Mathlib.Topology.Instances.Rat
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

/-! A countable dense subgroup of the intrinsic zero-sum l1 group. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace MeasureEquivalenceSolenoid

noncomputable section

def rationalFinite : (ℕ →₀ ℚ) →+ RealL1 :=
  Finsupp.liftAddHom (fun i =>
    (lp.singleAddMonoidHom (E := fun _ : ℕ => ℝ) 1 i).comp
      (Rat.castHom ℝ).toAddMonoidHom)

@[simp] theorem rationalFinite_single (i : ℕ) (q : ℚ) :
    rationalFinite (Finsupp.single i q) = lp.single 1 i (q:ℝ) := by
  exact Finsupp.liftAddHom_apply_single _ _ _



def zeroSumProjection : RealL1 →+ zeroSumSpace where
  toFun h := ⟨h - lp.single 1 0 ((lp.tsumCLM ℝ ℕ ℝ) h), by
    change (lp.tsumCLM ℝ ℕ ℝ) (h - lp.single 1 0 ((lp.tsumCLM ℝ ℕ ℝ) h)) = 0
    rw [map_sub]
    have hs (a : ℝ) : (lp.tsumCLM ℝ ℕ ℝ) (lp.single 1 0 a) = a := by
      simp [lp.tsumCLM_apply]
    rw [hs, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    change (0:RealL1) - lp.single 1 0 ((lp.tsumCLM ℝ ℕ ℝ) 0) = 0
    rw [map_zero, lp.single_zero, sub_zero]
  map_add' := by
    intro h k
    apply Subtype.ext
    simp only [map_add, lp.single_add, Submodule.coe_add]
    abel





def rationalZeroSum : (ℕ →₀ ℚ) →+ zeroSumSpace := zeroSumProjection.comp rationalFinite



def denseRationalSubgroup : AddSubgroup zeroSumSpace := rationalZeroSum.range

theorem denseRationalSubgroup_countable : (denseRationalSubgroup:Set zeroSumSpace).Countable :=
  Set.countable_range rationalZeroSum





end
end MeasureEquivalenceSolenoid


