-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.zero_or_conull_of_test_factorization
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:26:29.700414+00:00
-- url     : https://prove2.me/submissions/44a0a91d-319a-47d5-b36a-3ef9bda10f05

import Definitions.Def_BenchmarkOperator20261026_ConditionalFibers
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Tactic
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_determiningSet_generates

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

-- Preserved source skeleton: ConditionalFibers
section
/-! The actual invariant conditional kernel is constant almost everywhere
on almost every conditional fiber. Countability is used only for a family
that determines finite measures, so no AE/uncountable-forall swap is made. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceErgodicDecomposition

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]





theorem determiningSet_measurable (s : Finset ℕ) : MeasurableSet (determiningSet (Z := Z) s) :=
  s.measurableSet_biInter (fun i _hi => MeasurableSpace.measurableSet_natGeneratingSequence (α := Z) i)

theorem determiningSet_isPiSystem : IsPiSystem (range (determiningSet (Z := Z))) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _hne
  refine ⟨s ∪ t, ?_⟩
  ext z
  simp [determiningSet, Finset.mem_union, or_imp, forall_and]









end MeasureEquivalenceErgodicDecomposition

end

/-! A countable determining family suffices to test independence of an
invariant set from the whole sigma-algebra. -/
open MeasureTheory Set
open scoped ENNReal
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    (ν : Measure Z) [IsProbabilityMeasure ν]

theorem solution (B : Set Z) (hB : MeasurableSet B)
    (htest : ∀ s : Finset ℕ, ν.real (determiningSet s ∩ B) =
      ν.real (determiningSet s) * ν.real B) :
    ν B = 0 ∨ ν Bᶜ = 0 := by
  have heq : ν.restrict B = (ν B) • ν := by
    apply MeasureTheory.ext_of_generate_finite (range (determiningSet (Z := Z)))
      determiningSet_generates.symm determiningSet_isPiSystem
    · rintro _ ⟨s, rfl⟩
      rw [Measure.restrict_apply (determiningSet_measurable s), Measure.smul_apply, smul_eq_mul]
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν _)
        (ENNReal.mul_ne_top (measure_ne_top ν _) (measure_ne_top ν _))).mp
      rw [ENNReal.toReal_mul]
      exact (htest s).trans (mul_comm _ _)
    · simp
  have hBB : ν B = ν B * ν B := by
    have h := congrArg (fun ρ : Measure Z => ρ B) heq
    simpa only [Measure.restrict_apply hB, Set.inter_self, Measure.smul_apply, smul_eq_mul] using h
  have hr : ν.real B = ν.real B * ν.real B := by
    simpa only [ENNReal.toReal_mul, ← measureReal_def] using congrArg ENNReal.toReal hBB
  have hf : ν.real B * (ν.real B - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hz | ho
  · exact Or.inl ((measureReal_eq_zero_iff (measure_ne_top ν B)).mp hz)
  · right
    have hr1 : ν.real B = 1 := sub_eq_zero.mp ho
    have hb1 : ν B = 1 := (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν B)
      ENNReal.one_ne_top).mp (by simpa only [ENNReal.toReal_one] using hr1)
    rw [measure_compl hB (measure_ne_top ν B), measure_univ, hb1, tsub_self]
