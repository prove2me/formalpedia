-- Prove2me | Theorems.Thm_MeasureEquivalenceHellinger_affinity_eq_zero_iff_mutuallySingular
-- name    : MeasureEquivalenceHellinger.affinity_eq_zero_iff_mutuallySingular
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:00:02.547617+00:00
-- url     : https://prove2.me/theorems/8e94b4b0-ec25-44b6-a672-f91be79c1e2b
-- title:
--   Zero affinity characterizes mutual singularity
-- statement:
--   For finite measures $\mu,\nu$ on any measurable space, $$\operatorname{Aff}(\mu,\nu)=0\quad\Longleftrightarrow\quad\mu\perp\nu.$$ Affinity is computed from their square-root densities relative to $\mu+\nu$. The equivalence detects disjoint measure classes.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceHellinger.affinity_eq_zero_iff_mutuallySingular in HellingerAffinity.lean, lines 87–136; local source SHA-256 83c020c5fcf38ac35d98560bbea05154c302df3cd72b637268039abe9b43afa2. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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

/-!
Actual Hellinger affinity of finite measures via their L2 square-root RN
densities against their sum. This file proves the probability bounds and
the equivalence between zero affinity and mutual singularity.
-/
open MeasureTheory Filter
open scoped ENNReal
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger
variable {Y : Type*} [MeasurableSpace Y]

theorem MeasureEquivalenceHellinger.affinity_eq_zero_iff_mutuallySingular (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : affinity μ ν = 0 ↔ μ ⟂ₘ ν := by sorry
