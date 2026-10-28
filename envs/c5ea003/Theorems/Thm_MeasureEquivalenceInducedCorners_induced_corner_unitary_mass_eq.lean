-- Prove2me | Theorems.Thm_MeasureEquivalenceInducedCorners_induced_corner_unitary_mass_eq
-- name    : MeasureEquivalenceInducedCorners.induced_corner_unitary_mass_eq
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:03:01.979+00:00
-- url     : https://prove2.me/theorems/d7a8cb28-4524-48d3-a698-f1c2c64b7a6c
-- title:
--   Actual induced-corner intertwiners preserve finite mass
-- statement:
--   Let a countable group $G$ act measurably and preserve a sigma-finite measure $\mu$ on $X$. Let $A,B\subseteq X$ be measurable sets of finite measure. On $L^2((\mu|_A)\times\#G)$ and $L^2((\mu|_B)\times\#G)$, use the orbit observable $(x,g)\mapsto g\cdot x$ and the counting-index shift unitaries. If a genuine unitary $U$ intertwines all orbit-observable measurable projections and all index shifts, then
--   $$\mu(A)=\mu(B).$$
--   This is the finite-corner trace invariant, derived from the actual Hilbert-space operator rather than an assumed matrix field.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceInducedCorners.induced_corner_unitary_mass_eq in InducedCornerMassReflection.lean, lines 26–73; local source SHA-256 0d9c7a0a5cbb05cc13ba9984d1d96845306f9f9b7aec404eb2d69cafc1f44c80. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_InducedCornerUnitary
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

/-! A genuine unitary equivalence of induced corner modules preserves
their finite base measures. All coefficients, adjoints and Parseval
sums are those of the given unitary; no matrix field or trace is assumed. -/
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
open MeasureEquivalenceInducedCorners
open MeasureUnitary MeasureEquivalenceL2Restriction
  MeasureEquivalenceL2Coefficients MeasureEquivalenceL2Transport
variable {X G : Type*} [MeasurableSpace X] [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MulAction G X] [MeasurableConstSMul G X]
    (μ : Measure X) [SigmaFinite μ]
    (hmp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)

include hmp

theorem MeasureEquivalenceInducedCorners.induced_corner_unitary_mass_eq
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : μ A ≠ ∞) (hfinB : μ B ≠ ∞)
    (U : Lp ℂ 2 (cornerMeasure (G := G) μ A) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cornerMeasure (G := G) μ B))
    (hproj : ∀ (s : Set X) (hs : MeasurableSet s)
      (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)),
      U (indicatorL2 (cornerMeasure μ A) (hs.preimage orbitPoint_measurable) u) =
        indicatorL2 (cornerMeasure μ B) (hs.preimage orbitPoint_measurable) (U u))
    (hshift : ∀ (g : G) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)),
      U (inducedShiftUnitary μ A g u) = inducedShiftUnitary μ B g (U u)) :
    μ A = μ B := by sorry
