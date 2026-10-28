-- Prove2me | Definitions.Def_BenchmarkOperator20261026_GroupMarkov
-- name    : BenchmarkOperator20261026_GroupMarkov
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:28:45.461576+00:00
-- url     : https://prove2.me/theorems/abe7c2bf-d4a1-4d07-8b0c-fa48d4dd1b5c
-- title:
--   Group Markov
-- statement:
--   Chooses a natural-number enumeration of a countable group and defines the corresponding measurable move automorphisms of the acted-on space. The retained absolute-continuity fact verifies that these moves can be used in the Metropolis kernel for a nonsingular action.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization GroupMarkov.lean, lines 16–43; source SHA-256 96a824a3f5d07a497cc29cd607115ee8ce1a5d3f6d347e9368ef7457f61e740c. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Tactic

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

/-! The concrete stationary transition for one countable nonsingular
group action, with fixed space exactly its invariant L2 functions. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z]
    [MulAction G Z] [MeasurableConstSMul G Z]

noncomputable def groupEnumeration (G : Type*) [Group G] [Countable G] : ℕ → G :=
  (exists_surjective_nat G).choose



noncomputable def groupMoves : ℕ → Z ≃ᵐ Z :=
  fun n => (MeasurableEquiv.smul (groupEnumeration G n) : Z ≃ᵐ Z).symm



variable (μ : Measure Z)
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

include hns

theorem groupMoves_ac : ∀ n, μ.map (groupMoves (G := G) (Z := Z) n) ≪ μ := by
  intro n
  simpa only [groupMoves, MeasurableEquiv.symm_smul, MeasurableEquiv.smul_apply] using
    (hns (groupEnumeration G n)⁻¹).absolutelyContinuous







end MeasureEquivalenceMarkov


