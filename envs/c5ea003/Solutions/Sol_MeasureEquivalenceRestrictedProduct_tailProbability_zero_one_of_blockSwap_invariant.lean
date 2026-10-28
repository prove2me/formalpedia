-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.tailProbability_zero_one_of_blockSwap_invariant
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:40:46.861343+00:00
-- url     : https://prove2.me/submissions/a577754a-ecdd-4eb6-9949-16a3bafde520

import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPermutation
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
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_cylinder_blockSwap_independent
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_real_zero_one_of_approximants

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

-- Preserved source skeleton: RestrictedPermutation
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct















theorem measurable_permute (e : Equiv.Perm ℕ) : Measurable (permute e) :=
  measurable_pi_lambda _ (fun k => measurable_pi_apply (e k))

theorem measurePreserving_permute (e : Equiv.Perm ℕ) :
    MeasurePreserving (permute e) tailProbability tailProbability := by
  constructor
  · exact measurable_permute e
  · exact Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => baseMeasure) e.injective





end MeasureEquivalenceRestrictedProduct

end

open MeasureTheory Set Filter
open scoped ENNReal Topology symmDiff
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution (F : Set RealSequences)
    (hF : MeasurableSet F)
    (hinv : ∀ N, (permute (blockSwap N)) ⁻¹' F =ᵐ[tailProbability] F) :
    tailProbability F = 0 ∨ tailProbability Fᶜ = 0 := by
  have hreal : tailProbability.real F = 0 ∨ tailProbability.real F = 1 := by
    apply real_zero_one_of_approximants tailProbability F hF
    intro ε hε
    have hcover : ∃ D : Set (Set RealSequences), D.Countable ∧
        D ⊆ measurableCylinders (fun _ : ℕ => ℝ) ∧ tailProbability (⋃₀ D)ᶜ = 0 := by
      refine ⟨{univ}, countable_singleton _, ?_, by simp⟩
      intro s hs
      have hs' : s = univ := mem_singleton_iff.mp hs
      rw [hs']
      exact univ_mem_measurableCylinders _
    obtain ⟨B, hBC, hBF⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := tailProbability) isSetRing_measurableCylinders hcover
      generateFrom_measurableCylinders.symm hF (ENNReal.ofReal_pos.mpr hε)
    obtain ⟨s, A, hA, rfl⟩ := (mem_measurableCylinders B).mp hBC
    let B : Set RealSequences := cylinder s A
    let N : ℕ := s.sup id + 1
    let C : Set RealSequences := (permute (blockSwap N)) ⁻¹' B
    have hsN : s ⊆ Finset.range N := by
      intro k hk
      have hle : k ≤ s.sup id := Finset.le_sup (f := id) hk
      exact Finset.mem_range.mpr (by dsimp [N]; omega)
    have hBm : MeasurableSet B := hA.cylinder s
    have hCm : MeasurableSet C := (measurable_permute (blockSwap N)) hBm
    have hBr : tailProbability.real (F ∆ B) < ε := by
      have he := (ENNReal.toReal_lt_toReal (measure_ne_top tailProbability _)
        ENNReal.ofReal_ne_top).mpr hBF
      simpa only [Measure.real, ENNReal.toReal_ofReal hε.le, symmDiff_comm, B] using he
    have heq : F ∆ C =ᵐ[tailProbability] (permute (blockSwap N)) ⁻¹' (F ∆ B) := by
      simpa only [preimage_symmDiff, C] using
        (hinv N).symm.symmDiff (ae_eq_refl ((permute (blockSwap N)) ⁻¹' B))
    have hCr : tailProbability.real (F ∆ C) < ε := by
      calc
        tailProbability.real (F ∆ C) =
            tailProbability.real ((permute (blockSwap N)) ⁻¹' (F ∆ B)) :=
          measureReal_congr heq
        _ = tailProbability.real (F ∆ B) := by
          change (tailProbability ((permute (blockSwap N)) ⁻¹' (F ∆ B))).toReal =
            (tailProbability (F ∆ B)).toReal
          rw [← Measure.map_apply (measurable_permute (blockSwap N)) (hF.symmDiff hBm),
            (measurePreserving_permute (blockSwap N)).map_eq]
        _ < ε := hBr
    exact ⟨B, C, hBm, hCm, hBr, hCr, cylinder_blockSwap_independent s N hsN A hA⟩
  rcases hreal with h0 | h1
  · exact Or.inl ((measureReal_eq_zero_iff (measure_ne_top tailProbability F)).mp h0)
  · apply Or.inr
    apply (measureReal_eq_zero_iff (measure_ne_top tailProbability Fᶜ)).mp
    have he := measureReal_add_measureReal_compl (μ := tailProbability) hF
    have hu : tailProbability.real univ = 1 := by simp [Measure.real]
    rw [h1, hu] at he
    linarith
