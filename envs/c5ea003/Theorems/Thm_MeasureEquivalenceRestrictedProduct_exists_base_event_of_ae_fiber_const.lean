-- Prove2me | Theorems.Thm_MeasureEquivalenceRestrictedProduct_exists_base_event_of_ae_fiber_const
-- name    : MeasureEquivalenceRestrictedProduct.exists_base_event_of_ae_fiber_const
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:02:41.799071+00:00
-- url     : https://prove2.me/theorems/867b7a8b-6a6e-46b8-bae2-9ae64253fa77
-- title:
--   Almost-everywhere constant fibers give a measurable base event
-- statement:
--   Let $\mu$ and $\nu$ be s-finite measures on $\alpha$ and $\beta$, and let $\rho$ be a probability measure on $\beta$ with $\rho\ll\nu$. Let $E\subseteq\alpha\times\beta$ be measurable. If for $\mu$-almost every $x$ its section $E_x$ is null or conull for $\nu$, then a measurable set $A\subseteq\alpha$ satisfies
--   $$E=\{(x,y):x\in A\}\pmod{\mu\times\nu}.$$
--   The probability reference $\rho$ makes the base event measurable even when $\nu$ is infinite.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRestrictedProduct.exists_base_event_of_ae_fiber_const in FiberEventRepresentative.lean, lines 11–39; local source SHA-256 4a7bcb39945a9e38c81c96d99dd1c985fd3f63446e89a972abbcf5379ff67dc3. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem MeasureEquivalenceRestrictedProduct.exists_base_event_of_ae_fiber_const
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν ρ : Measure β) [SFinite μ] [SFinite ν] [IsProbabilityMeasure ρ]
    (hρ : ρ ≪ ν) (E : Set (α × β)) (hE : MeasurableSet E)
    (hc : ∀ᵐ x ∂μ, EventuallyConst (Prod.mk x ⁻¹' E) (ae ν)) :
    ∃ A : Set α, MeasurableSet A ∧ E =ᵐ[μ.prod ν] Prod.fst ⁻¹' A := by sorry
