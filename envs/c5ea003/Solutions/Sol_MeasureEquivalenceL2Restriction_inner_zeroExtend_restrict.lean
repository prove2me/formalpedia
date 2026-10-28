-- Prove2me | solution 1 for MeasureEquivalenceL2Restriction.inner_zeroExtend_restrict
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:32:31.054987+00:00
-- url     : https://prove2.me/submissions/8b360c83-1280-482a-9077-b0ff9ca94c70

import Definitions.Def_BenchmarkOperator20261026_L2RestrictionExtension
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.L2Space
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

/-! Actual bounded restriction and isometric zero extension for complex
L2 spaces, including their projection and adjoint identities. -/
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal
namespace MeasureEquivalenceL2Restriction
end MeasureEquivalenceL2Restriction
open MeasureEquivalenceL2Restriction
open MeasureUnitary
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem solution (A : Set X) (hA : MeasurableSet A)
    (f : Lp ℂ 2 (μ.restrict A)) (g : Lp ℂ 2 μ) :
    inner ℂ (zeroExtend μ A hA f) g = inner ℂ f (restrictMap μ A g) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℂ (zeroExtend μ A hA f x) (g x) ∂μ) =
        ∫ x, A.indicator (fun y => inner ℂ (f y) (g y)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [zeroExtend_coe μ A hA f] with x hx
      rw [hx]
      by_cases hxA : x ∈ A <;> simp [hxA]
    _ = ∫ x in A, inner ℂ (f x) (g x) ∂μ := integral_indicator hA
    _ = ∫ x in A, inner ℂ (f x) (restrictMap μ A g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [restrict_coe μ A g] with x hx
      rw [hx]
