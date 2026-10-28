-- Prove2me | Theorems.Thm_MeasureEquivalenceRigidity_ae_mem_of_root_mean_affinity
-- name    : MeasureEquivalenceRigidity.ae_mem_of_root_mean_affinity
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:08:48.846752+00:00
-- url     : https://prove2.me/theorems/76a38001-29ab-49fd-aa54-41c93820c4c2
-- title:
--   Vanishing mean deficits along algebraic roots force subgroup membership
-- statement:
--   Let $\mu$ be a probability measure and let $S_y$ be additive subgroups of an abelian group $K$. Fix $x\in K$ and roots $r_n\in K$ with natural multiplicities $m_n$ satisfying $m_nr_n=x$. Assume the sets $\{y:r_n\notin S_y\}$ are measurable. Suppose measurable functions $A_n:Y\to[0,1]$ vanish almost everywhere when $r_n\notin S_y$, and
--   $$1-\varepsilon_n\leq\int A_n\,d\mu,\qquad \varepsilon_n\longrightarrow0.$$
--   Then $x\in S_y$ for $\mu$-almost every $y$. The conclusion uses only the algebraic root identities and the averaged estimates.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRigidity.ae_mem_of_root_mean_affinity in RigidityRoots.lean, lines 118–154; local source SHA-256 2065c065a8ef889655833f9182163ac012be4432afb18eec37736d74e9464056. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.OrderClosed

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
The countable-roots step in the manuscript's quasi-invariance rigidity argument.

This module is a helper for Theorems 1.3 and 1.4. It does not assert the
ergodic decomposition, affinity estimate, or representation construction.
The hypotheses below are precisely the quantitative component estimates
needed after those analytic steps have been established.
-/
open Filter MeasureTheory
open scoped Topology ENNReal
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
variable {K : Type*} [AddCommGroup K]

theorem MeasureEquivalenceRigidity.ae_mem_of_root_mean_affinity
    [IsProbabilityMeasure μ]
    (S : Y → AddSubgroup K) (x : K) (root : ℕ → K)
    (multiplicity : ℕ → ℕ)
    (hroot : ∀ n, multiplicity n • root n = x)
    (A : ℕ → Y → ℝ)
    (hbad : ∀ n, MeasurableSet {y | root n ∉ S y})
    (hA : ∀ n, Measurable (A n))
    (hA_nonneg : ∀ n y, 0 ≤ A n y)
    (hA_le : ∀ n y, A n y ≤ 1)
    (hzero : ∀ n, ∀ᵐ y ∂μ, root n ∉ S y → A n y = 0)
    (ε : ℕ → ℝ)
    (hmean : ∀ n, 1 - ε n ≤ ∫ y, A n y ∂μ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂μ, x ∈ S y := by sorry
