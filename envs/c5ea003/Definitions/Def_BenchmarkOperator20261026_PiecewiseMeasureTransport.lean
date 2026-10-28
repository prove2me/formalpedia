-- Prove2me | Definitions.Def_BenchmarkOperator20261026_PiecewiseMeasureTransport
-- name    : BenchmarkOperator20261026_PiecewiseMeasureTransport
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:30:38.600985+00:00
-- url     : https://prove2.me/theorems/8346f926-4345-46d9-90dc-6a01454f343d
-- title:
--   Piecewise Measure Transport
-- statement:
--   Constructs the unitary pullback associated with measure-preserving maps that are inverses almost everywhere. The retained pullback inverse identity justifies the equivalence. The existence of suitable piecewise transports is a separate supporting theorem.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization PiecewiseMeasureTransport.lean, lines 112–126; source SHA-256 2edb1f31b6c71d14b0e796241b6d1bfb11745945cc8578d8c8cd9b2f5df444a1. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

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

/-! Countable equidecompositions give actual measure-preserving maps
with almost-everywhere inverses, and therefore genuine complex L2 unitaries. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceEquidecomposition

variable {X : Type*} [MeasurableSpace X]





section L2

variable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (F : X → Y) (H : Y → X)
    (hF : MeasurePreserving F μ ν) (hH : MeasurePreserving H ν μ)
    (hHF : ∀ᵐ x ∂μ, H (F x) = x) (hFH : ∀ᵐ y ∂ν, F (H y) = y)

include hHF in
theorem pullback_inverse (u : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving F hF (Lp.compMeasurePreserving H hH u) = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving H hH u) hF,
    hF.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving u hH), hHF]
    with x hx hu hxi
  simpa only [Function.comp_apply, hxi] using hx.trans hu

/-- Composition with actual inverse measure-preserving maps gives the
genuine complex L2 linear isometry equivalence used for induced modules. -/
noncomputable def pullbackUnitary : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ F hF) (by
    intro u
    exact ⟨Lp.compMeasurePreserving H hH u, pullback_inverse μ ν F H hF hH hHF u⟩)

end L2

end MeasureEquivalenceEquidecomposition


