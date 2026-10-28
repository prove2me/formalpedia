-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.real_zero_one_of_approximants
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:39:53.346268+00:00
-- url     : https://prove2.me/submissions/4d86b83b-0a88-4188-8728-b60d68cd4e2a

import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.Rat

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
open scoped ENNReal Topology symmDiff
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : Set α) (hF : MeasurableSet F)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ B C : Set α,
      MeasurableSet B ∧ MeasurableSet C ∧
      μ.real (F ∆ B) < ε ∧ μ.real (F ∆ C) < ε ∧
      μ.real (B ∩ C) = (μ.real B) ^ 2) :
    μ.real F = 0 ∨ μ.real F = 1 := by
  let p := μ.real F
  have hid : p = p ^ 2 := by
    by_contra hp
    have hd : 0 < |p - p ^ 2| := abs_pos.mpr (sub_ne_zero.mpr hp)
    let ε := |p - p ^ 2| / 8
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨B, C, hBm, hCm, hB, hC, hi⟩ := ha ε hε
    let b := μ.real B
    have hsub : F ∆ (B ∩ C) ⊆ (F ∆ B) ∪ (F ∆ C) := by
      intro x hx
      simp only [mem_symmDiff, mem_inter_iff, mem_union] at *
      tauto
    have hinter : |p - b ^ 2| < 2 * ε := by
      have hle : |p - b ^ 2| ≤ μ.real (F ∆ B) + μ.real (F ∆ C) := by
        calc
          |p - b ^ 2| = |μ.real F - μ.real (B ∩ C)| := by rw [hi]
          _ ≤ μ.real (F ∆ (B ∩ C)) :=
            abs_measureReal_sub_le_measureReal_symmDiff hF.nullMeasurableSet (hBm.inter hCm).nullMeasurableSet
          _ ≤ μ.real ((F ∆ B) ∪ (F ∆ C)) := measureReal_mono hsub
          _ ≤ μ.real (F ∆ B) + μ.real (F ∆ C) := measureReal_union_le _ _
      linarith
    have hbp : |b - p| ≤ ε := by
      have he := (abs_measureReal_sub_le_measureReal_symmDiff hF.nullMeasurableSet hBm.nullMeasurableSet).trans_lt hB
      exact (by simpa only [abs_sub_comm] using he.le)
    have hp0 : 0 ≤ p := measureReal_nonneg
    have hb0 : 0 ≤ b := measureReal_nonneg
    have hp1 : p ≤ 1 := measureReal_le_one
    have hb1 : b ≤ 1 := measureReal_le_one
    have hsq : |b ^ 2 - p ^ 2| ≤ 2 * ε := by
      calc
        |b ^ 2 - p ^ 2| = |b - p| * |b + p| := by rw [← abs_mul]; congr 1; ring
        _ ≤ ε * 2 := mul_le_mul hbp (abs_le.mpr ⟨by linarith, by linarith⟩)
          (abs_nonneg _) hε.le
        _ = 2 * ε := by ring
    have htri := abs_sub_le p (b ^ 2) (p ^ 2)
    dsimp only [ε] at hinter hsq
    linarith
  have he : p * (p - 1) = 0 := by nlinarith [hid]
  rcases mul_eq_zero.mp he with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)
