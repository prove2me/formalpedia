-- Prove2me | Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
-- name    : BenchmarkOperator20261026_SumFiberCoordinates
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:41:16.291811+00:00
-- url     : https://prove2.me/theorems/7a51161c-b7d9-462e-9697-49bd51f83807
-- title:
--   Sum Fiber Coordinates
-- statement:
--   Defines the sum-fiber coordinate equivalence in the presence of an auxiliary parameter, and retains its forward and inverse formulas. These coordinates are used to state the finite-head invariance arguments.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization SumFiberCoordinates.lean, lines 10–23; source SHA-256 cfa67862cbd7ecb0dfc60f341be57a02bf17afbe66381a437cba2c380823e183. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RationalFiberErgodic
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
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

def sumFiberEquiv (n : ℕ) (α : Type*) [MeasurableSpace α] :
    ((Fin (n + 1) → ℝ) × α) ≃ᵐ ((ℝ × α) × (Fin n → ℝ)) :=
  ((sumTailEquiv n).prodCongr (MeasurableEquiv.refl α)).trans
    (MeasurableEquiv.prodAssoc.trans
      (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm).trans
        MeasurableEquiv.prodAssoc.symm))

@[simp] theorem sumFiberEquiv_apply (n : ℕ) {α : Type*} [MeasurableSpace α]
    (x : (Fin (n + 1) → ℝ) × α) :
    sumFiberEquiv n α x = ((∑ i, x.1 i, x.2), fun i => x.1 i.succ) := rfl

@[simp] theorem sumFiberEquiv_symm_apply (n : ℕ) {α : Type*} [MeasurableSpace α]
    (x : (ℝ × α) × (Fin n → ℝ)) :
    (sumFiberEquiv n α).symm x = (Fin.cons (x.1.1 - ∑ i, x.2 i) x.2, x.1.2) := rfl



end MeasureEquivalenceRestrictedProduct


