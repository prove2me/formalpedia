-- Prove2me | Theorems.Thm_MeasureEquivalenceL2Transport_twisted_coefficient_constant_norm_eq_adjoint
-- name    : MeasureEquivalenceL2Transport.twisted_coefficient_constant_norm_eq_adjoint
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:02:43.418997+00:00
-- url     : https://prove2.me/theorems/f7995c26-1a13-4bed-a0fd-ca0d05a1e409
-- title:
--   Equal constant-vector norms for twisted coefficients
-- statement:
--   Let $d,e$ be measure-preserving measurable automorphisms of $(X,\mu)$, let $A,B$ be measurable with finite mass, and let $T:L^2(\mu|_A)\to L^2(\mu|_B)$ be bounded. Assume $T$ intertwines multiplication projections pulled back along $e$ and $d$ for every measurable set. Then $$\|T1_A\|_2=\|T^*1_B\|_2.$$ This derives the coefficient norm equality from an actual operator intertwining hypothesis.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceL2Transport.twisted_coefficient_constant_norm_eq_adjoint in L2TransportedNorms.lean, lines 68–109; local source SHA-256 29ace16c031d8016cb317c0bebe54200ad97780a4b39350e8b13ee367fc765b6. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_L2FiniteOnes
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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

/-! The two constant-vector norms of one genuine twisted matrix
coefficient agree. The proof uses finite-support compression and the
commutative multiplication algebra, instead of postulating a trace. -/
open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1500000
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
open MeasureEquivalenceL2Transport
open MeasureEquivalenceL2Restriction MeasureEquivalenceEquidecomposition MeasureUnitary
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem MeasureEquivalenceL2Transport.twisted_coefficient_constant_norm_eq_adjoint
    (d e : X ≃ᵐ X) (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : μ A ≠ ∞) (hfinB : μ B ≠ ∞)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) (hs.preimage e.measurable) f) =
        indicatorL2 (μ.restrict B) (hs.preimage d.measurable) (T f)) :
    ‖T (restrictedOne μ A hfinA)‖ = ‖T.adjoint (restrictedOne μ B hfinB)‖ := by sorry
