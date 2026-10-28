-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
-- name    : BenchmarkOperator20261026_MeasureCantorDenseFamily
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:35:23.411813+00:00
-- url     : https://prove2.me/theorems/b7fd04fe-7b35-41a4-9945-7b2ef4e2da28
-- title:
--   Measure Cantor Dense Family
-- statement:
--   Defines the cylinder-indicator fundamental vectors in amplified Cantor $L^2$, their countable enumeration and sequence, and the resulting Hilbert basis and coordinate equivalence. The retained density and infinite-rank facts justify these pointwise constructions. Their Borel dependence is addressed in later theorem nodes.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasureCantorDenseFamily.lean, lines 14–153; source SHA-256 b937432bf06c8c81cc427b1c20e3ddf5b2fb82b13de4c5785cf30d40303862ef. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureGramSchmidtBorel
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
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

/-! A countable cylinder-indicator fundamental family in the actual
infinite-multiplicity L² fibers. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

theorem cantorCylinder_isSetAlgebra : IsSetAlgebra (Set.range cantorCylinder) where
  empty_mem := ⟨⟨∅, ∅⟩, cylinder_empty ∅⟩
  compl_mem := by
    rintro s ⟨⟨I, S⟩, rfl⟩
    exact ⟨⟨I, Sᶜ⟩, (compl_cylinder (α := fun _ : ℕ => Bool) I S).symm⟩
  union_mem := by
    classical
    rintro s t ⟨⟨I, S⟩, rfl⟩ ⟨⟨J, T⟩, rfl⟩
    exact ⟨⟨I ∪ J, Finset.restrict₂ (π := fun _ : ℕ => Bool) (Finset.subset_union_left (s₁ := I) (s₂ := J)) ⁻¹' S ∪
      Finset.restrict₂ (π := fun _ : ℕ => Bool) (Finset.subset_union_right (s₁ := I) (s₂ := J)) ⁻¹' T⟩,
      (union_cylinder (α := fun _ : ℕ => Bool) I J S T).symm⟩

theorem cantorCylinder_measureDense (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    μ.MeasureDense (Set.range cantorCylinder) :=
  Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ cantorCylinder_isSetAlgebra
    cantorCylinder_generates.symm

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def indicatorConstantCLM {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    E →L[ℂ] Lp E 2 μ := by
  let L : E →ₗ[ℂ] Lp E 2 μ := {
    toFun := indicatorConstLp 2 hs hμs
    map_add' := fun _ _ => indicatorConstLp_add.symm
    map_smul' := by
      intro c v
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c • v),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := v),
        Lp.coeFn_smul c (indicatorConstLp 2 hs hμs v)] with x hcv hv hc
      simp only [Pi.smul_apply] at hc
      simp only [RingHom.id_apply]
      rw [hcv, hc, hv]
      by_cases hx : x ∈ s <;> simp [hx] }
  exact L.mkContinuous (μ.real s ^ (1 / (2 : ℝ))) (fun v => by
    change ‖indicatorConstLp 2 hs hμs v‖ ≤ _
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    exact le_of_eq (mul_comm _ _))

abbrev CantorFundamentalIndex := CantorCylinderIndex × ℕ

local instance cantorFiberMeasurable (μ : Measure CantorSpace) :
    MeasurableSpace (Lp OperatorCoding.CanonicalHilbert 2 μ) := borel _

local instance cantorFiberBorelSpace (μ : Measure CantorSpace) :
    BorelSpace (Lp OperatorCoding.CanonicalHilbert 2 μ) := ⟨rfl⟩

noncomputable def cantorFundamentalVector (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (k : CantorFundamentalIndex) : Lp OperatorCoding.CanonicalHilbert 2 μ :=
  indicatorConstLp 2 (cantorCylinder_measurable k.1) (measure_ne_top μ _)
    (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)

noncomputable def cantorFundamentalClosedSpan (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    Submodule ℂ (Lp OperatorCoding.CanonicalHilbert 2 μ) :=
  (Submodule.span ℂ (Set.range (cantorFundamentalVector μ))).topologicalClosure

theorem cantorFundamentalClosedSpan_indicator (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (k : CantorCylinderIndex) (v : OperatorCoding.CanonicalHilbert) :
    indicatorConstLp 2 (cantorCylinder_measurable k) (measure_ne_top μ _) v ∈
      cantorFundamentalClosedSpan μ := by
  let L : OperatorCoding.CanonicalHilbert →L[ℂ] Lp OperatorCoding.CanonicalHilbert 2 μ :=
    indicatorConstantCLM μ (cantorCylinder_measurable k) (measure_ne_top μ _)
  have hsum := L.hasSum (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) v)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hsum
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro n hn
  have he : (lp.single 2 n (v n) : OperatorCoding.CanonicalHilbert) =
      (v n) • (lp.single 2 n (1 : ℂ) : OperatorCoding.CanonicalHilbert) := by
    simpa using (lp.single_smul (E := fun _ : ℕ => ℂ) 2 n (v n) (1 : ℂ))
  rw [he, L.map_smul]
  apply Submodule.smul_mem
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨(k, n), rfl⟩

theorem cantorFundamentalClosedSpan_all_indicators (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (v : OperatorCoding.CanonicalHilbert) {s : Set CantorSpace} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) : indicatorConstLp 2 hs hμs v ∈ cantorFundamentalClosedSpan μ := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have ha := (cantorCylinder_measureDense μ).indicatorConstLp_subset_closure 2 v
    (show indicatorConstLp 2 hs hμs v ∈
      {indicatorConstLp 2 ht hμt v | (t : Set CantorSpace) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)}
      from ⟨s, hs, hμs, rfl⟩)
  apply closure_minimal (t := (cantorFundamentalClosedSpan μ : Set _)) ?_
    (Submodule.isClosed_topologicalClosure _) ha
  rintro x ⟨t, ht, hμt, rfl⟩
  obtain ⟨k, rfl⟩ := ht
  exact cantorFundamentalClosedSpan_indicator μ k v

theorem cantorFundamentalVector_dense_span (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (cantorFundamentalVector μ))).topologicalClosure = ⊤ := by
  have hall : ∀ f : Lp OperatorCoding.CanonicalHilbert 2 μ, f ∈ cantorFundamentalClosedSpan μ := by
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (fun f : Lp OperatorCoding.CanonicalHilbert 2 μ => f ∈ cantorFundamentalClosedSpan μ)
    · intro v s hs hμs
      exact cantorFundamentalClosedSpan_all_indicators μ v hs hμs.ne
    · intro f g hf hg hdis hfm hgm
      exact Submodule.add_mem _ hfm hgm
    · exact Submodule.isClosed_topologicalClosure _
  apply top_unique
  intro f hf
  exact hall f

instance cantorFundamentalIndex_nonempty : Nonempty CantorFundamentalIndex :=
  ⟨(⟨∅, Set.univ⟩, 0)⟩

noncomputable def cantorFundamentalEnumeration : ℕ → CantorFundamentalIndex :=
  (exists_surjective_nat CantorFundamentalIndex).choose

theorem cantorFundamentalEnumeration_surjective : Function.Surjective cantorFundamentalEnumeration :=
  (exists_surjective_nat CantorFundamentalIndex).choose_spec

noncomputable def cantorFundamentalSequence (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    ℕ → Lp OperatorCoding.CanonicalHilbert 2 μ :=
  cantorFundamentalVector μ ∘ cantorFundamentalEnumeration

theorem cantorFundamentalSequence_dense_span (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (cantorFundamentalSequence μ))).topologicalClosure = ⊤ := by
  unfold cantorFundamentalSequence
  rw [Function.Surjective.range_comp cantorFundamentalEnumeration_surjective]
  exact cantorFundamentalVector_dense_span μ

theorem cantorFundamentalSequence_nonzero_infinite (μ : Measure CantorSpace) [IsProbabilityMeasure μ] :
    {i | InnerProductSpace.gramSchmidtNormed ℂ (cantorFundamentalSequence μ) i ≠ 0}.Infinite :=
  gramSchmidtNormed_nonzero_infinite (cantorFundamentalSequence μ)
    (cantorFundamentalSequence_dense_span μ) (amplifiedL2_not_finiteDimensional μ)

noncomputable def cantorFiberBasis (μ : Measure CantorSpace) [IsProbabilityMeasure μ] :
    HilbertBasis ℕ ℂ (Lp OperatorCoding.CanonicalHilbert 2 μ) :=
  HilbertBasis.mk
    (selectedGramSchmidt_orthonormal (fun _ : Unit => cantorFundamentalSequence μ)
      (fun _ => cantorFundamentalSequence_nonzero_infinite μ) ()) (by
        rw [selectedGramSchmidt_span, cantorFundamentalSequence_dense_span])

noncomputable def cantorFiberCoordinates (μ : Measure CantorSpace) [IsProbabilityMeasure μ] :
    Lp OperatorCoding.CanonicalHilbert 2 μ ≃ₗᵢ[ℂ] OperatorCoding.CanonicalHilbert :=
  (cantorFiberBasis μ).repr

end

end MeasureUnitary


