-- Prove2me | solution 1 for condExp_piFinset_eq_marginal
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T07:19:24.024328+00:00
-- url     : https://prove2.me/submissions/e070204f-4448-4174-a979-d5d4da014b39

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_condExp_comap_fst_eq_partial_integral

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) {Z : (∀ i, α i) → ℝ}
    (hZ : Integrable Z (Measure.pi μ)) :
    (Measure.pi μ)[Z | MeasurableSpace.comap (Finset.restrict s) inferInstance]
      =ᵐ[Measure.pi μ]
      fun ω => ∫ z : (∀ i : {i // ¬ i ∈ s}, α i),
          Z ((MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s)).symm
              ((MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s) ω).1, z))
          ∂(Measure.pi fun i : {i // ¬ i ∈ s} => μ i) := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd α (· ∈ s) with he
  set ρ : Measure (∀ i : ↥s, α i) :=
    @Measure.pi ↥s (fun i : ↥s => α i) (Subtype.fintype (· ∈ s))
      (fun i : ↥s => inferInstance) (fun i : ↥s => μ i) with hρ
  set σ := Measure.pi fun i : {i // ¬ i ∈ s} => μ i with hσ
  have mpe : MeasurePreserving e (Measure.pi μ) (ρ.prod σ) := by
    rw [hρ, hσ, he]; exact measurePreserving_piEquivPiSubtypeProd μ (· ∈ s)
  haveI : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  haveI : IsProbabilityMeasure σ := by rw [hσ]; infer_instance
  set F : (∀ i : ↥s, α i) × (∀ i : {i // ¬ i ∈ s}, α i) → ℝ :=
    fun q => Z (e.symm q) with hF
  have hZeq : Z = F ∘ e := by ext ω; simp [hF, he]
  have hFint : Integrable F (ρ.prod σ) := by
    rw [← mpe.integrable_comp_emb e.measurableEmbedding (g := F)]
    rw [← hZeq]; exact hZ
  set g : (∀ i, α i) → ℝ := fun ω => ∫ z, F ((e ω).1, z) ∂σ with hg
  have hcomap : MeasurableSpace.comap (Finset.restrict s)
      (inferInstance : MeasurableSpace (∀ i : ↥s, α i))
      = MeasurableSpace.comap e (MeasurableSpace.comap Prod.fst inferInstance) := by
    rw [MeasurableSpace.comap_comp]; rfl
  have hm : MeasurableSpace.comap (Finset.restrict s)
      (inferInstance : MeasurableSpace (∀ i : ↥s, α i))
      ≤ (inferInstance : MeasurableSpace (∀ i, α i)) :=
    (Finset.measurable_restrict s).comap_le
  set W' : (∀ i : ↥s, α i) × (∀ i : {i // ¬ i ∈ s}, α i) → ℝ :=
    fun q => ∫ y, F (q.1, y) ∂σ with hW'
  have hg_comp : g = W' ∘ e := by ext ω; simp [hg, hW', Function.comp]
  have hbrick : (ρ.prod σ)[F | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ρ.prod σ] W' :=
    condExp_comap_fst_eq_partial_integral ρ σ hFint
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hZ ?_ ?_ ?_).symm
  · intro t _ _
    have hW'int : Integrable W' (ρ.prod σ) := (integrable_condExp).congr hbrick
    have : Integrable g (Measure.pi μ) := by
      rw [hg_comp]; exact mpe.integrable_comp_of_integrable hW'int
    exact this.integrableOn
  · intro t ht _
    rw [hcomap] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have htrans_g : ∫ ω in e ⁻¹' u, g ω ∂(Measure.pi μ) = ∫ q in u, W' q ∂(ρ.prod σ) := by
      rw [hg_comp]; exact mpe.setIntegral_preimage_emb e.measurableEmbedding W' u
    have htrans_Z : ∫ ω in e ⁻¹' u, Z ω ∂(Measure.pi μ) = ∫ q in u, F q ∂(ρ.prod σ) := by
      rw [hZeq]; exact mpe.setIntegral_preimage_emb e.measurableEmbedding F u
    rw [htrans_g, htrans_Z]
    have hu_fst : MeasurableSet[MeasurableSpace.comap Prod.fst inferInstance] u := hu
    have hmfst : MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace _)
        ≤ (inferInstance : MeasurableSpace ((∀ i : ↥s, α i) × (∀ i : {i // ¬ i ∈ s}, α i))) :=
      measurable_fst.comap_le
    calc ∫ q in u, W' q ∂(ρ.prod σ)
        = ∫ q in u, ((ρ.prod σ)[F | MeasurableSpace.comap Prod.fst inferInstance]) q ∂(ρ.prod σ) := by
          exact integral_congr_ae (ae_restrict_of_ae hbrick.symm)
      _ = ∫ q in u, F q ∂(ρ.prod σ) := setIntegral_condExp hmfst hFint hu_fst
  · rw [hcomap]
    set h := (ρ.prod σ)[F | MeasurableSpace.comap Prod.fst inferInstance] with hh
    have hh_sm : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance] h :=
      stronglyMeasurable_condExp
    have he_meas :
        @Measurable _ _ (MeasurableSpace.comap e (MeasurableSpace.comap Prod.fst inferInstance))
          (MeasurableSpace.comap Prod.fst inferInstance) e :=
      Measurable.of_comap_le le_rfl
    have hcomp_sm :
        StronglyMeasurable[MeasurableSpace.comap e (MeasurableSpace.comap Prod.fst inferInstance)]
          (h ∘ e) := hh_sm.comp_measurable he_meas
    have hg_ae : g =ᵐ[Measure.pi μ] (h ∘ e) := by
      rw [hg_comp]
      exact mpe.quasiMeasurePreserving.ae_eq_comp (g := W') (g' := h) hbrick.symm
    exact ⟨h ∘ e, hcomp_sm, hg_ae⟩
