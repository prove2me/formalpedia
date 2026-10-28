-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedErgodic
-- name    : BenchmarkOperator20261026_RestrictedErgodic
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:48:20.719566+00:00
-- url     : https://prove2.me/theorems/52ed3cc4-7a2a-47f3-a6ab-8c91d1661b6d
-- title:
--   Restricted Ergodic
-- statement:
--   Defines the corresponding finite-vector block swap and retains its involution identity. These finite permutation data are used in subsequent invariance arguments for restricted-product events.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedErgodic.lean, lines 11–27; source SHA-256 1f015e13bc03b7ff93c631aa6a5af031db0038764d8b8482a9e5ac863c153d5f. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPermutation
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Rat

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

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def finBlockSwapFun (M : ℕ) (i : Fin (2 * M + 1)) : Fin (2 * M + 1) :=
  ⟨blockSwap M i, by
    have hi := i.isLt
    change blockSwapFun M i < 2 * M + 1
    unfold blockSwapFun
    split_ifs <;> omega⟩

theorem finBlockSwapFun_involutive (M : ℕ) : Function.Involutive (finBlockSwapFun M) := by
  intro i
  apply Fin.ext
  exact blockSwap_involutive M i

def finBlockSwap (M : ℕ) : Equiv.Perm (Fin (2 * M + 1)) where
  toFun := finBlockSwapFun M
  invFun := finBlockSwapFun M
  left_inv := finBlockSwapFun_involutive M
  right_inv := finBlockSwapFun_involutive M







end MeasureEquivalenceRestrictedProduct


