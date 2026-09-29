-- Prove2me | solution 1 for condExp_comap_fst_eq_partial_integral
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T07:15:56.470695+00:00
-- url     : https://prove2.me/submissions/77f2b170-1563-4fbf-8d5d-8b4176ca71a2

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (σ : Measure γ) [IsProbabilityMeasure σ]
    {W : β × γ → ℝ} (hW : Integrable W (ρ.prod σ)) :
    (ρ.prod σ)[W | MeasurableSpace.comap Prod.fst inferInstance]
      =ᵐ[ρ.prod σ] fun p => ∫ y, W (p.1, y) ∂σ := by
  classical
  have hfst_m : @Measurable _ _ (MeasurableSpace.comap Prod.fst inferInstance) _
      (Prod.fst : β × γ → β) := Measurable.of_comap_le le_rfl
  have hm : MeasurableSpace.comap Prod.fst inferInstance
      ≤ (inferInstance : MeasurableSpace (β × γ)) := measurable_fst.comap_le
  set g0 : β → ℝ := fun b => ∫ y, W (b, y) ∂σ with hg0_def
  have hg0int : Integrable g0 ρ := hW.integral_prod_left
  set g0' : β → ℝ := hg0int.aestronglyMeasurable.mk g0 with hg0'_def
  have hg0'sm : StronglyMeasurable g0' := hg0int.aestronglyMeasurable.stronglyMeasurable_mk
  have hg0eq : g0' =ᵐ[ρ] g0 := hg0int.aestronglyMeasurable.ae_eq_mk.symm
  set g : β × γ → ℝ := fun p => g0 p.1 with hg_def
  have hfstmp : MeasurePreserving (Prod.fst : β × γ → β) (ρ.prod σ) ρ :=
    measurePreserving_fst
  have hgm_sm : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
      (fun p : β × γ => g0' p.1) := hg0'sm.comp_measurable hfst_m
  have hg_ae : (fun p : β × γ => g0' p.1) =ᵐ[ρ.prod σ] g := by
    have := hfstmp.quasiMeasurePreserving.ae_eq_comp (g := g0') (g' := g0) hg0eq
    simpa [hg_def, Function.comp] using this
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance] g (ρ.prod σ) :=
    ⟨fun p => g0' p.1, hgm_sm, hg_ae.symm⟩
  have hgint : Integrable g (ρ.prod σ) := by
    have : Integrable (fun p : β × γ => g0 p.1) (ρ.prod σ) :=
      hfstmp.integrable_comp_of_integrable hg0int
    simpa [hg_def, Function.comp] using this
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hW ?_ ?_ hgm).symm
  · intro s _ _; exact hgint.integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := hs
    have hpre : (Prod.fst : β × γ → β) ⁻¹' t = t ×ˢ Set.univ := by
      ext ⟨b, c⟩; simp
    rw [hpre]
    have hrestrict : (ρ.prod σ).restrict (t ×ˢ Set.univ)
        = (ρ.restrict t).prod (σ.restrict Set.univ) := (Measure.prod_restrict _ _).symm
    rw [hrestrict, Measure.restrict_univ]
    have hWon : Integrable W ((ρ.restrict t).prod σ) := by
      have := hW.integrableOn (s := t ×ˢ Set.univ)
      rwa [IntegrableOn, hrestrict, Measure.restrict_univ] at this
    have hgon : Integrable g ((ρ.restrict t).prod σ) := by
      have := hgint.integrableOn (s := t ×ˢ Set.univ)
      rwa [IntegrableOn, hrestrict, Measure.restrict_univ] at this
    rw [integral_prod g hgon, integral_prod W hWon]
    refine integral_congr_ae (.of_forall (fun b => ?_))
    simp only [hg_def, hg0_def, integral_const, probReal_univ, smul_eq_mul, one_mul]
