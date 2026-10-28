-- Prove2me | Theorems.Thm_MeasureEquivalenceMarkov_couplingTransition_ae_eq_integral_kernel
-- name    : MeasureEquivalenceMarkov.couplingTransition_ae_eq_integral_kernel
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:57:42.582012+00:00
-- url     : https://prove2.me/theorems/8539796a-7392-41fd-825d-d2d76af3db09
-- title:
--   The stationary coupling contraction is kernel integration
-- statement:
--   Let $\mu$ be finite and let a coupling $J$ on $Z\times Z$ have both marginals equal to $\mu$. Suppose a finite kernel $\kappa$ disintegrates it as $J=\mu\otimes\kappa$. The $L^2$ contraction $P_J$ defined by the adjoints of the coordinate pullbacks satisfies
--   $$P_Jf(z)=\int f(y)\,d\kappa_z(y)\quad\mu\text{-almost everywhere}
--   \qquad(f\in L^2(\mu;\mathbb R)).$$
--   This identifies the Hilbert-space transition with a common pointwise formula on conditional components.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceMarkov.couplingTransition_ae_eq_integral_kernel in CouplingKernel.lean, lines 37–64; local source SHA-256 065e16b21f4e084d85f34698c3e02a3160b1bbc25d1180c5eb358fd950065ce8. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_CouplingMarkov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
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

/-! The L2 coupling transition is the actual pointwise kernel integral. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal InnerProduct
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
open MeasureEquivalenceMarkov
variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

theorem MeasureEquivalenceMarkov.couplingTransition_ae_eq_integral_kernel
    (κ : Kernel Z Z) [IsFiniteKernel κ] (hJ : J = μ ⊗ₘ κ)
    (f : Lp ℝ 2 μ) :
    couplingTransition μ J hfst hsnd f =ᵐ[μ] fun z => ∫ y, f y ∂κ z := by sorry
