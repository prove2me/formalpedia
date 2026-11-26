-- Prove2me | solution 1 for ReweightedNPMLE.measure_projection_regular_zero_locus_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:14:19.688795+00:00
-- url     : https://prove2.me/submissions/2073fb82-a545-4a02-b455-eef34ff3f770

import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.HausdorffDimension

-- Inline helpers preserved from ReweightedNPMLE.AnalyticIncidence.
section
/-!
# Analytic derivative detection for incidence sets

A nontrivial globally real-analytic scalar function has a nonzero derivative
of some finite order at every point. This supplies the minimal derivative
order used to turn possibly singular zero sets into regular level sets.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology ENNReal NNReal

namespace ReweightedNPMLE









theorem measure_image_eq_zero_of_lipschitzOn_dimension_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [IsAddHaarMeasure μ] (f : E → F) (U : Set E) {K : ℝ≥0}
    (hf : LipschitzOnWith K f U)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F) : μ (f '' U) = 0 := by
  letI : ProperSpace F := FiniteDimensional.proper_rclike ℝ F
  have hdim' : (Module.finrank ℝ E : ℝ≥0∞) < Module.finrank ℝ F := by exact_mod_cast hdim
  have hless : dimH (f '' U) < Module.finrank ℝ F :=
    (hf.dimH_image_le.trans ((dimH_mono (subset_univ U)).trans_eq
      (Real.dimH_univ_eq_finrank E))).trans_lt hdim'
  have hzero : (Measure.hausdorffMeasure (Module.finrank ℝ F)) (f '' U) = 0 :=
    hausdorffMeasure_of_dimH_lt (d := (Module.finrank ℝ F : ℝ≥0)) hless
  exact (absolutelyContinuous_isAddHaarMeasure μ (Measure.hausdorffMeasure
    (Module.finrank ℝ F))) hzero

end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.IncidenceProjection.
section
/-!
# Null projections of regular level sets

The implicit function theorem parameterizes a regular level set locally by
the kernel of its derivative. Strict differentiability of this chart gives
a Lipschitz neighborhood, whose lower-dimensional image is Haar-null.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

theorem exists_open_null_projection_neighborhood_of_regular_zero
    {X H D : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D]
    (μ : Measure D) [IsAddHaarMeasure μ] (π : X →L[ℝ] D)
    (g : X → H) (L : X →L[ℝ] H) (a : X)
    (hg : HasStrictFDerivAt g L a) (hL : Function.Surjective L) (ha : g a = 0)
    (hdim : Module.finrank ℝ X < Module.finrank ℝ D + Module.finrank ℝ H) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ μ (π '' (U ∩ g ⁻¹' {0})) = 0 := by
  letI : CompleteSpace X := FiniteDimensional.complete ℝ X
  have hrange : L.range = ⊤ := LinearMap.range_eq_top.mpr hL
  have hker : Module.finrank ℝ L.ker < Module.finrank ℝ D := by
    have hrank := L.toLinearMap.finrank_range_add_finrank_ker
    rw [hrange, finrank_top] at hrank
    omega
  let φ : L.ker → X := hg.implicitFunction g L hrange 0
  have hφ : HasStrictFDerivAt φ L.ker.subtypeL 0 := by
    simpa only [ha] using hg.to_implicitFunction hrange
  obtain ⟨K, V, hV, hφlip⟩ := hφ.exists_lipschitzOnWith
  let e := hg.implicitToOpenPartialHomeomorph g L hrange
  let κ : X → L.ker := fun x ↦ (e x).2
  have hκ : ContinuousAt κ a :=
    (e.continuousAt (hg.mem_implicitToOpenPartialHomeomorph_source hrange)).snd
  have hκa : κ a = 0 := by
    simp [κ, e, hg.implicitToOpenPartialHomeomorph_self hrange]
  have hpre : {x | κ x ∈ V} ∈ 𝓝 a := by
    apply hκ.preimage_mem_nhds
    simpa only [hκa] using hV
  have heq : ∀ᶠ x in 𝓝 a, hg.implicitFunction g L hrange (g x) (κ x) = x :=
    hg.eq_implicitFunction hrange
  have hnb : {x | κ x ∈ V ∧ hg.implicitFunction g L hrange (g x) (κ x) = x} ∈ 𝓝 a :=
    inter_mem hpre heq
  obtain ⟨U, hUsub, hUopen, haU⟩ := mem_nhds_iff.mp hnb
  have hprojLip : LipschitzOnWith (‖π‖₊ * K) (π ∘ φ) V :=
    π.lipschitz.lipschitzOnWith.comp hφlip (mapsTo_univ _ _)
  have hnull := measure_image_eq_zero_of_lipschitzOn_dimension_lt μ (π ∘ φ) V hprojLip hker
  refine ⟨U, hUopen, haU, measure_mono_null ?_ hnull⟩
  rintro z ⟨x, ⟨hxU, hxzero⟩, rfl⟩
  have hx := hUsub hxU
  refine ⟨κ x, hx.1, ?_⟩
  have hxg : g x = 0 := hxzero
  exact congrArg π (by simpa only [hxg] using hx.2)



end ReweightedNPMLE
end

/-!
# Null projections of regular level sets

The implicit function theorem parameterizes a regular level set locally by
the kernel of its derivative. Strict differentiability of this chart gives
a Lipschitz neighborhood, whose lower-dimensional image is Haar-null.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Countable subcovers promote the local implicit-function null projections
to a null projection of the entire regular zero locus. -/
theorem solution
    {X H D : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D]
    (μ : Measure D) [IsAddHaarMeasure μ] (π : X →L[ℝ] D)
    (g : X → H) (hg : ContDiff ℝ 1 g)
    (hdim : Module.finrank ℝ X < Module.finrank ℝ D + Module.finrank ℝ H) :
    μ (π '' {x | g x = 0 ∧ Function.Surjective (fderiv ℝ g x)}) = 0 := by
  classical
  let S : Set X := {x | g x = 0 ∧ Function.Surjective (fderiv ℝ g x)}
  have hlocal : ∀ a : S, ∃ U : Set X, IsOpen U ∧ a.val ∈ U ∧ μ (π '' (U ∩ g ⁻¹' {0})) = 0 :=
    fun a ↦ exists_open_null_projection_neighborhood_of_regular_zero μ π g (fderiv ℝ g a.val)
      a.val (hg.contDiffAt.hasStrictFDerivAt (by norm_num)) a.property.2 a.property.1 hdim
  choose U hUopen haU hUnull using hlocal
  have hcover : S ⊆ ⋃ a : S, U a := fun a ha ↦ mem_iUnion.mpr ⟨⟨a, ha⟩, haU ⟨a, ha⟩⟩
  obtain ⟨c, hc, hccover⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    U hUopen hcover
  have hnull : μ (⋃ a ∈ c, π '' (U a ∩ g ⁻¹' {0})) = 0 :=
    (measure_biUnion_null_iff hc).mpr (fun a _ ↦ hUnull a)
  apply measure_mono_null _ hnull
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hccover hx)
  obtain ⟨hac, hxU⟩ := mem_iUnion.mp ha
  exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨hac, ⟨x, ⟨hxU, hx.1⟩, rfl⟩⟩⟩
