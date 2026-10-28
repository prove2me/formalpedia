-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
-- name    : BenchmarkOperator20261026_OrbitMarkov
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:28:13.335834+00:00
-- url     : https://prove2.me/theorems/84f774e5-7837-4a13-a94a-d15bda40d176
-- title:
--   Orbit Markov
-- statement:
--   Defines the countable move relation and a Metropolis kernel obtained from the normalized coupling construction. The retained finiteness facts and Markov-kernel instance make these objects available to the later stationary averaging arguments.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OrbitMarkov.lean, lines 16–119; source SHA-256 59f7e114fc169a67ea834ad174e6408cacca8014451a51d7ddf1d5c967d63629. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_CouplingMixture
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Disintegration.Unique
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

/-! The actual Markov kernel of the Metropolis coupling stays in the
countable move relation and preserves the original measure. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]

def moveRelation (e : ℕ → Z ≃ᵐ Z) (x y : Z) : Prop :=
  x = y ∨ ∃ n, y = e n x ∨ y = (e n).symm x







theorem finiteMeasure_of_fst (μ : Measure Z) [IsFiniteMeasure μ]
    (J : Measure (Z × Z)) (hfst : J.map Prod.fst = μ) : IsFiniteMeasure J := by
  have hfinite : IsFiniteMeasure (J.map Prod.fst) := by rw [hfst]; infer_instance
  exact (Measure.isFiniteMeasure_map_iff measurable_fst.aemeasurable).mp hfinite

section Kernel

variable [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (J : Measure (Z × Z)) [IsFiniteMeasure J]
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)









end Kernel

section ConcreteKernel

variable [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (e : ℕ → Z ≃ᵐ Z)
    (hmap : ∀ n, μ.map (e n) ≪ μ)

include hmap in
theorem normalizedMetropolisCoupling_finite : IsFiniteMeasure (normalizedMetropolisCoupling μ e) :=
  finiteMeasure_of_fst μ _ (normalizedMetropolisCoupling_marginals μ e hmap).1

/-- The actual regular conditional transition kernel of the concrete
normalized stationary Metropolis coupling. -/
noncomputable def metropolisKernel : Kernel Z Z :=
  letI := normalizedMetropolisCoupling_finite μ e hmap
  (normalizedMetropolisCoupling μ e).condKernel

instance metropolisKernel_markov : IsMarkovKernel (metropolisKernel μ e hmap) := by
  letI := normalizedMetropolisCoupling_finite μ e hmap
  unfold metropolisKernel
  infer_instance











end ConcreteKernel

end MeasureEquivalenceMarkov


