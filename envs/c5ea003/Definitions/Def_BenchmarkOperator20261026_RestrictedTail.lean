-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedTail
-- name    : BenchmarkOperator20261026_RestrictedTail
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:39:23.968451+00:00
-- url     : https://prove2.me/theorems/87ad551e-a236-454d-837a-5d85c4f70fb3
-- title:
--   Restricted Tail
-- statement:
--   Retains the product-measure identity for splitting an infinite product indexed by a disjoint sum into the corresponding two product factors. This identity is used to compare finite-head and infinite-tail decompositions.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedTail.lean, lines 12–33; source SHA-256 74701b7aed1e0324f560320ee7a36a150f7f1d4a9d80bbde6bd550366f889ff1. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ProductMeasure
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

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem infinitePi_sum {α β : Type*} (μ : α → Measure ℝ) (ν : β → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm =
      Measure.infinitePi (Sum.elim μ ν) := by
  letI (i : α ⊕ β) : IsProbabilityMeasure (Sum.elim μ ν i) := by
    cases i <;> dsimp <;> infer_instance
  apply Measure.eq_infinitePi
  intro s t ht
  have hpre : (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm ⁻¹'
      Set.pi s t = Set.pi s.toLeft (fun i => t (.inl i)) ×ˢ
        Set.pi s.toRight (fun j => t (.inr j)) := by
    ext z
    simp [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi,
      Set.mem_pi, Sum.forall]
  rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable
    (MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht i)), hpre,
    Measure.prod_prod,
    Measure.infinitePi_pi μ (fun i _ => ht (.inl i)),
    Measure.infinitePi_pi ν (fun j _ => ht (.inr j))]
  exact (Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight s
    (fun i => Sum.elim μ ν i (t i))).symm

end MeasureEquivalenceRestrictedProduct


