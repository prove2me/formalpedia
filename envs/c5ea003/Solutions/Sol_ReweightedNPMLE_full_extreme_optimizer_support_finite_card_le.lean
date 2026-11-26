-- Prove2me | solution 1 for ReweightedNPMLE.full_extreme_optimizer_support_finite_card_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:02:06.131891+00:00
-- url     : https://prove2.me/submissions/c73cef66-f360-4231-9761-7ddc97cbf2fb

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_probability_optimizer_not_extreme_of_disjoint_positive_regions

-- Inline helpers preserved from ReweightedNPMLE.ProbabilityFiberGeometry.
section
/-!
# Real-vector-space geometry of full probability fibers

Integration against continuous test functions embeds probability measures
injectively into a locally convex real vector space with its product topology.
The weakly compact mixture fiber has a compact convex image. Extreme points
are thus mathlib extreme points of a faithful representation of the full
probability-measure fiber, rather than of a finite coefficient simplex.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





theorem probabilityIntegralFunctional_injective {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    Function.Injective (probabilityIntegralFunctional (Θ := Θ)) := by
  intro μ ν h
  have hh : μ.toFiniteMeasure = ν.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq (fun f ↦ congrFun h f.toContinuousMap)
  apply ProbabilityMeasure.toMeasure_injective
  exact congrArg (fun ρ : FiniteMeasure Θ ↦ (ρ : Measure Θ)) hh











theorem isExtremeProbabilityMixture_mem_fiber {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ)
    (hμ : IsExtremeProbabilityMixture A v μ) : μ ∈ probabilityMixtureFiber A v := by
  obtain ⟨ν, hν, heq⟩ := hμ.1
  exact probabilityIntegralFunctional_injective heq ▸ hν









end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FullExtremeSupport.
section
/-!
# Finite support of every full-measure extreme optimizer

Distinct support points have disjoint positive-mass metric neighborhoods.
The partition perturbation theorem excludes more than `n` such points,
including infinitely many support points. Consequently every full-fiber
extreme optimizer has finite topological support of cardinality at most `n`.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

theorem exists_disjoint_open_neighborhoods_of_finite_injective {Θ : Type*}
    [MetricSpace Θ] {m : ℕ} [Nonempty (Fin m)]
    (θ : Fin m → Θ) (hθ : Function.Injective θ) :
    ∃ E : Fin m → Set Θ, (∀ j, IsOpen (E j) ∧ θ j ∈ E j) ∧
      Pairwise (fun j k ↦ Disjoint (E j) (E k)) := by
  classical
  let d : Fin m × Fin m → ℝ := fun p ↦ if p.1 = p.2 then 1 else dist (θ p.1) (θ p.2)
  have hd : ∀ p, 0 < d p := by
    intro p
    dsimp [d]
    split_ifs with h
    · norm_num
    · exact dist_pos.mpr (fun hh ↦ h (hθ hh))
  let S : Finset ℝ := Finset.univ.image d
  have hSne : S.Nonempty := Finset.univ_nonempty.image d
  let δ := S.min' hSne
  have hδ : 0 < δ := by
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp (Finset.min'_mem S hSne)
    dsimp only [δ]
    rw [← heq]
    exact hd p
  have hδle : ∀ j k, δ ≤ d (j, k) := fun j k ↦
    Finset.min'_le S (d (j, k)) (Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩)
  refine ⟨fun j ↦ Metric.ball (θ j) (δ / 3), ?_, ?_⟩
  · intro j
    exact ⟨Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩
  · intro j k hjk
    have hh := hδle j k
    dsimp [d] at hh
    rw [if_neg hjk] at hh
    exact Metric.ball_disjoint_ball (by linarith)

theorem full_extreme_optimizer_no_large_injective_support {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n < m)
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hext : IsExtremeProbabilityMixture A v μ)
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (hθS : ∀ j, θ j ∈ (μ : Measure Θ).support) : False := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨E, hE, hEd⟩ := exists_disjoint_open_neighborhoods_of_finite_injective θ hθ
  have hEpos : ∀ j, 0 < (μ : Measure Θ) (E j) := fun j ↦
    (Measure.mem_support_iff_forall (θ j)).mp (hθS j) (E j) ((hE j).1.mem_nhds (hE j).2)
  exact probability_optimizer_not_extreme_of_disjoint_positive_regions hmn A hA hC hCpos hAC
    w v hw hvmax μ (isExtremeProbabilityMixture_mem_fiber A v μ hext) E
    (fun j ↦ (hE j).1.measurableSet) hEd hEpos hext









end ReweightedNPMLE
end

/-!
# Finite support of every full-measure extreme optimizer

Distinct support points have disjoint positive-mass metric neighborhoods.
The partition perturbation theorem excludes more than `n` such points,
including infinitely many support points. Consequently every full-fiber
extreme optimizer has finite topological support of cardinality at most `n`.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hext : IsExtremeProbabilityMixture A v μ) :
    (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ n := by
  classical
  let T := (μ : Measure Θ).support
  have hfinite : T.Finite := by
    by_contra hinfinite
    letI : Infinite T := Set.infinite_coe_iff.mpr hinfinite
    let e := Infinite.natEmbedding T
    let θ : Fin (n + 1) → Θ := fun j ↦ (e j.val).val
    have hθ : Function.Injective θ := by
      intro j k hjk
      apply Fin.ext
      exact e.injective (Subtype.ext hjk)
    exact full_extreme_optimizer_no_large_injective_support (Nat.lt_succ_self n)
      A hA hC hCpos hAC w v hw hvmax μ hext θ hθ (fun j ↦ (e j.val).property)
  letI : Fintype T := hfinite.fintype
  have hcard : Fintype.card T ≤ n := by
    by_contra hle
    let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
    let θ : Fin (Fintype.card T) → Θ := fun j ↦ (e j).val
    have hθ : Function.Injective θ := fun j k hjk ↦ e.injective (Subtype.ext hjk)
    exact full_extreme_optimizer_no_large_injective_support (lt_of_not_ge hle)
      A hA hC hCpos hAC w v hw hvmax μ hext θ hθ (fun j ↦ (e j).property)
  refine ⟨hfinite, ?_⟩
  change T.ncard ≤ n
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact hcard
