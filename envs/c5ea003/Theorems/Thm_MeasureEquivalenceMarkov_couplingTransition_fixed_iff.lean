-- Prove2me | Theorems.Thm_MeasureEquivalenceMarkov_couplingTransition_fixed_iff
-- name    : MeasureEquivalenceMarkov.couplingTransition_fixed_iff
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:57:44.034487+00:00
-- url     : https://prove2.me/theorems/6cb47321-4ca7-4e6f-a262-4b7bc6195df4
-- title:
--   Fixed vectors of a stationary coupling
-- statement:
--   Let $J$ be a measure on $Z\times Z$ whose two marginals equal a measure $\mu$. Let $i,j:L^2(\mu;\mathbb R)\to L^2(J;\mathbb R)$ be the first- and second-coordinate isometric pullbacks, and put $P_J=i^*j$. Then
--   $$P_Jf=f\quad\Longleftrightarrow\quad f(x)=f(y)\quad J\text{-almost everywhere}.$$
--   This translates the fixed space of a contraction into invariance along its coupling edges.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceMarkov.couplingTransition_fixed_iff in CouplingMarkov.lean, lines 85–105; local source SHA-256 f9c4422667f745a33ac0a658feb1fb3b6073105756dcd4a80186d4b0ce2cb76b. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_CouplingMarkov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
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
A stationary coupling gives an actual contraction of L2. The operator
is the adjoint of the first-coordinate pullback followed by the
second-coordinate pullback. Its fixed vectors are precisely the
functions with equal pullbacks on the coupling.
-/
open MeasureTheory Filter
open scoped InnerProduct
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
open MeasureEquivalenceMarkov
variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

theorem MeasureEquivalenceMarkov.couplingTransition_fixed_iff (f : Lp ℝ 2 μ) :
    couplingTransition μ J hfst hsnd f = f ↔
      ∀ᵐ z ∂J, f z.1 = f z.2 := by sorry
