-- Prove2me | solution 1 for MeasureEquivalenceDensity.squareMeasure_injective_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:15:49.464494+00:00
-- url     : https://prove2.me/submissions/2c89380f-bad2-4ec0-bdfe-4f7fee35244f

import Definitions.Def_BenchmarkOperator20261026_DensityMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
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

/-! Concrete finite measures with an L2 square density. -/
open MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
open MeasureEquivalenceDensity
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem solution [SigmaFinite μ] :
    Set.InjOn (squareMeasure μ) (Set.Ici (0 : Lp ℝ 2 μ)) := by
  intro f hf g hg hfg
  have heq : μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2)) =
      μ.withDensity (fun x => ENNReal.ofReal (g x ^ 2)) :=
    congrArg (fun ν : FiniteMeasure α => (ν : Measure α)) hfg
  have hae := (withDensity_eq_iff_of_sigmaFinite
    ((Lp.aestronglyMeasurable f).aemeasurable.pow_const 2).ennreal_ofReal
    ((Lp.aestronglyMeasurable g).aemeasurable.pow_const 2).ennreal_ofReal).mp heq
  apply Lp.ext
  filter_upwards [hae, (Lp.coeFn_nonneg f).mpr hf,
    (Lp.coeFn_nonneg g).mpr hg] with x h1 h2 h3
  change 0 ≤ f x at h2
  change 0 ≤ g x at h3
  have hs := congrArg ENNReal.toReal h1
  simp only [ENNReal.toReal_ofReal (sq_nonneg (f x)),
    ENNReal.toReal_ofReal (sq_nonneg (g x))] at hs
  nlinarith
