-- Prove2me | Theorems.Thm_MeasureEquivalenceErgodicDecomposition_invariantConditionalKernel_affinity
-- name    : MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_affinity
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:58:57.60336+00:00
-- url     : https://prove2.me/theorems/b371b6ac-071f-4153-a598-678dc731cf07
-- title:
--   Affinity over invariant conditional probabilities
-- statement:
--   Let a group $G$ act on a countably generated standard Borel space $Z$, let $\mu$ be finite, and let $\kappa_x$ be its conditional probabilities over the invariant sigma-algebra. Suppose a measurable automorphism $e$ fixes every invariant measurable event modulo $\mu$-null sets. Then $$\operatorname{Aff}(\mu,e_*\mu)=\int_Z\operatorname{Aff}(\kappa_x,e_*\kappa_x)\,d\mu(x).$$ This relates global affinity to the actual invariant components.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_affinity in InvariantAffinity.lean, lines 46–76; local source SHA-256 7eace7e1036af03383222d16848ba850c1cff3259542db24eccaff0f96ec2644. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Condexp
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

/-! Affinity disintegration over the actual invariant sigma algebra.
Exceptional sets may depend on the invariant event; no uncountable
intersection of conull sets is taken. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceHellinger
variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] [MeasurableSpace.CountablyGenerated Z]
    (μ : Measure Z) [IsFiniteMeasure μ]

theorem MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_affinity (e : Z ≃ᵐ Z)
    (hinv : ∀ s : Set Z, MeasurableSet[invariantSigma (G := G)] s →
      e ⁻¹' s =ᵐ[μ] s) :
    affinity μ (μ.map e) =
      ∫ x, affinity (invariantConditionalKernel (G := G) μ x)
        ((invariantConditionalKernel (G := G) μ x).map e) ∂μ := by sorry
