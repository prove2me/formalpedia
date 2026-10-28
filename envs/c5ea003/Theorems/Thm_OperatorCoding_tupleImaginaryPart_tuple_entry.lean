-- Prove2me | Theorems.Thm_OperatorCoding_tupleImaginaryPart_tuple_entry
-- name    : OperatorCoding.tupleImaginaryPart_tuple_entry
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:12:35.715573+00:00
-- url     : https://prove2.me/theorems/fe4ac088-bf3c-4270-9900-71679b316d2e
-- title:
--   The coding operator contains every unitary tuple entry
-- statement:
--   Let $(u_n)$ be a sequence of unitaries on a complex Hilbert space $H$, and let $B_u$ be the constructed imaginary-part operator on $\ell_2(\mathbb N;H)$. For every $n\in\mathbb N$ and $x\in H$,
--   $$(B_u\delta_{2n+2}x)_{2n+1}=\frac1{16}\,2^{-n}u_nx.$$
--   Thus the bounded coding operator retains each original unitary with an explicit nonzero coefficient, which makes simultaneous conjugacy recoverable.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration OperatorCoding.tupleImaginaryPart_tuple_entry in OperatorCoefficients.lean, lines 86–113; local source SHA-256 c00cd3b70a50e860d857b4a24f3acc6ec3c7ce5d719ce00f4b3435d3681afa20. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorSeries
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
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

/-! Matrix entries of the actual norm-convergent operator coding. -/
open ContinuousLinearMap
namespace OperatorCoding
end OperatorCoding
open OperatorCoding
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OperatorCoding.tupleImaginaryPart_tuple_entry (u : ℕ → StrongUnitary H) (n : ℕ) (x : H) :
    tupleImaginaryPart u (lp.single 2 (2 * n + 2) x) (2 * n + 1) =
      ((((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ)) • u n x := by sorry
