-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasureGramSchmidtBorel
-- name    : BenchmarkOperator20261026_MeasureGramSchmidtBorel
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:32:31.399554+00:00
-- url     : https://prove2.me/theorems/0926f146-caab-438a-9a69-c8d09aad3418
-- title:
--   Measure Gram Schmidt Borel
-- statement:
--   Defines the Gram–Schmidt sequence with its zero terms removed and the corresponding Hilbert basis under the stated density and infinite-rank hypotheses. The retained orthonormality and span facts justify the basis construction. Measurable selection assertions are separate theorem nodes.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasureGramSchmidtBorel.lean, lines 75–163; source SHA-256 7ea95ae5a507f10812fc04e774d16f379f04128c5fb636ebbfc691a7e6f579ce. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

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

/-! Borel Gram–Schmidt and Borel removal of its zero vectors.
These are fixed-fiber results; a parameter-dependent L² trivialization still
requires a measurable dense fundamental family. -/

open MeasureTheory InnerProductSpace Set Finset

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]









noncomputable def selectedGramSchmidt (f : S → ℕ → E) (s : S) (n : ℕ) : E :=
  gramSchmidtNormed ℂ (f s) (Nat.nth (fun i => gramSchmidtNormed ℂ (f s) i ≠ 0) n)



theorem selectedGramSchmidt_orthonormal (f : S → ℕ → E)
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite) (s : S) :
    Orthonormal ℂ (selectedGramSchmidt f s) := by
  classical
  let g : ℕ → {i | gramSchmidtNormed ℂ (f s) i ≠ 0} :=
    fun n => ⟨Nat.nth (fun i => gramSchmidtNormed ℂ (f s) i ≠ 0) n,
      Nat.nth_mem_of_infinite (hinf s) n⟩
  have hg : Function.Injective g := by
    intro i j h
    exact (Nat.nth_strictMono (hinf s)).injective (congrArg Subtype.val h)
  exact (gramSchmidtNormed_orthonormal' (𝕜 := ℂ) (f s)).comp g hg

theorem selectedGramSchmidt_span (f : S → ℕ → E) (s : S) :
    Submodule.span ℂ (Set.range (selectedGramSchmidt f s)) =
      Submodule.span ℂ (Set.range (f s)) := by
  classical
  calc
    Submodule.span ℂ (Set.range (selectedGramSchmidt f s)) =
        Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (f s))) := by
      apply le_antisymm
      · apply Submodule.span_mono
        rintro x ⟨n, rfl⟩
        exact ⟨_, rfl⟩
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        by_cases hi : gramSchmidtNormed ℂ (f s) i = 0
        · rw [hi]
          exact Submodule.zero_mem _
        · have hx : gramSchmidtNormed ℂ (f s) i = selectedGramSchmidt f s
              (Nat.count (fun j => gramSchmidtNormed ℂ (f s) j ≠ 0) i) := by
            unfold selectedGramSchmidt
            rw [Nat.nth_count hi]
          rw [hx]
          exact Submodule.subset_span ⟨_, rfl⟩
    _ = Submodule.span ℂ (Set.range (gramSchmidt ℂ (f s))) :=
      span_gramSchmidtNormed_range (f s)
    _ = Submodule.span ℂ (Set.range (f s)) := span_gramSchmidt ℂ (f s)

noncomputable def selectedGramSchmidtBasis [CompleteSpace E] (f : S → ℕ → E)
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite)
    (hdense : ∀ s, (Submodule.span ℂ (Set.range (f s))).topologicalClosure = ⊤)
    (s : S) : HilbertBasis ℕ ℂ E :=
  HilbertBasis.mk (selectedGramSchmidt_orthonormal f hinf s) (by
    rw [selectedGramSchmidt_span, hdense s])



theorem gramSchmidtNormed_nonzero_infinite (f : ℕ → E)
    (hdense : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤)
    (hinfinite : ¬ FiniteDimensional ℂ E) :
    {i | gramSchmidtNormed ℂ f i ≠ 0}.Infinite := by
  classical
  intro hfinite
  have hfiniteRange : (Set.range (gramSchmidtNormed ℂ f)).Finite := by
    apply (hfinite.image (gramSchmidtNormed ℂ f)).insert (0 : E) |>.subset
    rintro x ⟨i, rfl⟩
    by_cases hi : gramSchmidtNormed ℂ f i = 0
    · exact Set.mem_insert_iff.mpr (Or.inl hi)
    · exact Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩
  letI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f))) :=
    FiniteDimensional.span_of_finite ℂ hfiniteRange
  have hspan : Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f)) = ⊤ := by
    rw [← (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f))).closed_of_finiteDimensional.submodule_topologicalClosure_eq,
      span_gramSchmidtNormed_range, span_gramSchmidt, hdense]
  apply hinfinite
  apply Module.Finite.of_surjective (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f))).subtype
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ f)) := by rw [hspan]; trivial
  exact ⟨⟨x, hx⟩, rfl⟩



end MeasureUnitary


