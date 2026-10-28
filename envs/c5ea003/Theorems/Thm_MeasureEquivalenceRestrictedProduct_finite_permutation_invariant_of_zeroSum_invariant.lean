-- Prove2me | Theorems.Thm_MeasureEquivalenceRestrictedProduct_finite_permutation_invariant_of_zeroSum_invariant
-- name    : MeasureEquivalenceRestrictedProduct.finite_permutation_invariant_of_zeroSum_invariant
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:03:15.237862+00:00
-- url     : https://prove2.me/theorems/d9262025-1abd-41b7-8881-7c25c97fe095
-- title:
--   Rational zero-sum invariance implies finite-coordinate permutation invariance
-- statement:
--   Let $\mu$ be an s-finite measure on a measurable space $\alpha$. Let $E\subseteq\mathbb R^{n+1}\times\alpha$ be measurable and invariant almost everywhere, with respect to Lebesgue measure times $\mu$, under every rational zero-sum translation of the real coordinates. Then for every permutation $p$ of those coordinates,
--   $$1_E((x_{p(i)})_i,a)=1_E(x,a)\quad\text{almost everywhere}.$$
--   This extracts finite permutation symmetry from the zero-sum translation action.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRestrictedProduct.finite_permutation_invariant_of_zeroSum_invariant in ZeroSumFiberEvent.lean, lines 51–79; local source SHA-256 89d983e0b737b4677496a10b06caeff190c6a2bcb49f1af390a227d398677353. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
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
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem MeasureEquivalenceRestrictedProduct.finite_permutation_invariant_of_zeroSum_invariant
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set ((Fin (n + 1) → ℝ) × α)) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin (n + 1) → ℚ, (∑ i, q i) = 0 →
      (fun z : (Fin (n + 1) → ℝ) × α => (z.1 + fun i => (q i : ℝ), z.2)) ⁻¹' E
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ] E)
    (p : Equiv.Perm (Fin (n + 1))) :
    (fun z : (Fin (n + 1) → ℝ) × α => (fun i => z.1 (p i), z.2)) ⁻¹' E
      =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ] E := by sorry
