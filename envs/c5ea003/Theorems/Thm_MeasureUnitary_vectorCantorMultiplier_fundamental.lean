-- Prove2me | Theorems.Thm_MeasureUnitary_vectorCantorMultiplier_fundamental
-- name    : MeasureUnitary.vectorCantorMultiplier_fundamental
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:11:41.528002+00:00
-- url     : https://prove2.me/theorems/7b01b4aa-7b95-47ae-997c-ace6e4d5567c
-- title:
--   Cylinder phase multipliers act explicitly on the fundamental $L^2$ family
-- statement:
--   Let $\mu$ be a finite measure on Cantor space, let $C,D$ belong to the cylinder algebra, and let $e_j$ be a standard vector of the canonical infinite-dimensional Hilbert space. Multiplication by the phase $1_C-1_{C^c}$ sends the fundamental vector $1_De_j$ to
--   $$(1_C-1_{C^c})(1_De_j)=1_{C\cap D}e_j-1_{C^c\cap D}e_j$$
--   in the Hilbert-valued space $L^2(\mu)$. The identity gives explicit, measurable Gram-matrix formulas for the varying-measure unitary family.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureUnitary.vectorCantorMultiplier_fundamental in MeasureCantorGram.lean, lines 49–75; local source SHA-256 3b323f9a79d29963b3b41bd2db4dd34026e6e00d881c7baaa04d0743ac6249db. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorAmplified
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorGram
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

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

/-! Measurable Gram matrices for the explicit varying-measure L² family.
The parameter measurable structure is the genuine Giry structure on
probability measures, and all entries are actual L² inner products. -/
open MeasureTheory Set Filter
open scoped ENNReal
namespace MeasureUnitary
end MeasureUnitary
open MeasureUnitary

theorem MeasureUnitary.vectorCantorMultiplier_fundamental (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (r : CantorCylinderIndex) (k : CantorFundamentalIndex) :
    vectorCantorMultiplier μ r (cantorFundamentalVector μ k) =
      cantorFundamentalVector μ (cantorIntersectionIndex r k.1, k.2) -
        cantorFundamentalVector μ (cantorIntersectionIndex (cantorComplementIndex r) k.1, k.2) := by sorry
