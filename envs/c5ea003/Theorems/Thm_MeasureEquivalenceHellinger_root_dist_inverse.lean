-- Prove2me | Theorems.Thm_MeasureEquivalenceHellinger_root_dist_inverse
-- name    : MeasureEquivalenceHellinger.root_dist_inverse
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:55:23.555891+00:00
-- url     : https://prove2.me/theorems/ea6d21f7-50f6-4bc7-a1b8-bc6cc3bb9ba2
-- title:
--   Hellinger root distance is preserved by simultaneous inversion
-- statement:
--   Let $e,f$ be commuting measurable automorphisms of a measurable space, and let $\rho$ be a finite measure quasi-invariant under both automorphisms and their inverses. Writing $r_\rho(\lambda)=\sqrt{d\lambda/d\rho}$ as an element of real $L^2(\rho)$, one has
--   $$\|r_\rho((e^{-1})_*\rho)-r_\rho((f^{-1})_*\rho)\|_2
--   =\|r_\rho(e_*\rho)-r_\rho(f_*\rho)\|_2.$$
--   The identity supplies the inverse-distance condition required by the density-graph construction.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceHellinger.root_dist_inverse in HellingerTransport.lean, lines 129–154; local source SHA-256 aebe47b1dae35755a8fd7d184ecf358eaa4b24986823d5e276f7ac2ce4923d17. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
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

open MeasureTheory Filter
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem MeasureEquivalenceHellinger.root_dist_inverse (e f : α ≃ᵐ α) (ρ : Measure α) [IsFiniteMeasure ρ]
    (hcomm : Function.Commute e f)
    (he : ρ.map e ≪ ρ) (hf : ρ.map f ≪ ρ)
    (hei : ρ.map e.symm ≪ ρ) (hfi : ρ.map f.symm ≪ ρ) :
    dist (root (ρ.map e.symm) ρ) (root (ρ.map f.symm) ρ) =
      dist (root (ρ.map e) ρ) (root (ρ.map f) ρ) := by sorry
