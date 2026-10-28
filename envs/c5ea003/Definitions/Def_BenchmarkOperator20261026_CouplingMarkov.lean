-- Prove2me | Definitions.Def_BenchmarkOperator20261026_CouplingMarkov
-- name    : BenchmarkOperator20261026_CouplingMarkov
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:27:04.754385+00:00
-- url     : https://prove2.me/theorems/f5afa9bf-4578-4c55-8011-3df8715eea00
-- title:
--   Coupling Markov
-- statement:
--   Defines the two isometric coordinate pullbacks associated with a coupling having equal marginals, and their adjoint composite on real $L^2$. The same construction is defined abstractly for two isometric embeddings into a common Hilbert space. Fixed-vector characterizations are separate supporting theorems.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization CouplingMarkov.lean, lines 23–80; source SHA-256 f9c4422667f745a33ac0a658feb1fb3b6073105756dcd4a80186d4b0ce2cb76b. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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

section Hilbert

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The contraction determined by two isometric embeddings into one
Hilbert space. -/
noncomputable def isometryTransition (i j : E →ₗᵢ[ℝ] F) : E →L[ℝ] E :=
  i.toContinuousLinearMap.adjoint ∘L j.toContinuousLinearMap





end Hilbert

section Coupling

variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

/-- First-coordinate L2 pullback for an actual coupling with marginal μ. -/
noncomputable def couplingFirst : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 J :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst ⟨measurable_fst, hfst⟩

/-- Second-coordinate L2 pullback. -/
noncomputable def couplingSecond : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 J :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.snd ⟨measurable_snd, hsnd⟩

/-- The actual L2 transition operator determined by a stationary coupling. -/
noncomputable def couplingTransition : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  isometryTransition (couplingFirst μ J hfst) (couplingSecond μ J hsnd)





end Coupling

end MeasureEquivalenceMarkov


