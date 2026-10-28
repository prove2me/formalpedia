-- Prove2me | solution 1 for MeasureEquivalenceSolenoid.twoPoint_limit
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:11:12.615361+00:00
-- url     : https://prove2.me/submissions/8107d71a-1767-4985-86c0-ff0aebdad942

import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
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
end MeasureEquivalenceSolenoid
open MeasureEquivalenceSolenoid

theorem solution (a : ℝ) :
    Tendsto (fun n => l1Embedding (twoPoint a n)) atTop (𝓝 (coordinateShift a)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with n hn
  have hi : i ≠ n+1 := by omega
  change realCharacter ((lp.single 1 0 a : RealL1) i) = realCharacter ((twoPoint a n) i)
  congr 1
  change (lp.single 1 0 a : RealL1) i =
    (lp.single 1 0 a : RealL1) i - (lp.single 1 (n+1) a : RealL1) i
  have hz : (lp.single 1 (n+1) a : RealL1) i = 0 :=
    lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 (n+1) a hi
  rw [hz, sub_zero]
