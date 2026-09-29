-- Prove2me | solution 1 for dlp_sigma_randomization_condexp_eq_sigma_integral
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T04:17:40.88515+00:00
-- url     : https://prove2.me/submissions/5eb7eb26-f957-4f32-b03a-7e019773c9a3

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
Direct proof of `dlp_sigma_randomization_condexp_eq_sigma_integral`
(σ-conditional-expectation substrate; node to be created).

Strategy (de la Peña–Montgomery-Smith 1995 eq (4)→(6), measure-theoretic core):
- the σ-block coordinate `Prod.snd` is independent of the sample block `Prod.fst`
  under the product measure `μ.prod ν` (`ProbabilityTheory.indepFun_prod`);
- `g ∘ Prod.snd` is measurable w.r.t. the σ-block σ-algebra `comap Prod.snd`;
- `MeasureTheory.condExp_indep_eq` ⇒ `E( g∘snd | comap fst ) = ∫ (g∘snd) d(μ.prod ν)` a.e.;
- Fubini (`integral_prod`) + `μ` a probability measure ⇒ `∫ (g∘snd) d(μ.prod ν) = ∫ g dν`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution
    {Ω B E : Type*}
    [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : B → E) (hgm : StronglyMeasurable g) (hgi : Integrable g ν) :
    (μ.prod ν)[fun ab : Ω × B => g ab.2 |
        MeasurableSpace.comap (Prod.fst : Ω × B → Ω) mΩ]
      =ᵐ[μ.prod ν] fun _ => ∫ b, g b ∂ν := by
  have hsnd_meas : @Measurable (Ω × B) B _ _ Prod.snd := measurable_snd
  have hfst_meas : @Measurable (Ω × B) Ω _ _ Prod.fst := measurable_fst
  -- σ-block independent of sample block under the product measure
  have hIF : (fun ab : Ω × B => ab.2) ⟂ᵢ[μ.prod ν] (fun ab : Ω × B => ab.1) := by
    have := indepFun_prod (μ := μ) (ν := ν) (X := (id : Ω → Ω)) (Y := (id : B → B))
      measurable_id measurable_id
    exact this.symm
  have hindep : Indep (MeasurableSpace.comap (Prod.snd : Ω × B → B) mB)
      (MeasurableSpace.comap (Prod.fst : Ω × B → Ω) mΩ) (μ.prod ν) := by
    rw [IndepFun_iff_Indep] at hIF
    exact hIF
  have hf_meas : StronglyMeasurable[MeasurableSpace.comap (Prod.snd : Ω × B → B) mB]
      (fun ab : Ω × B => g ab.2) :=
    hgm.comp_measurable (Measurable.of_comap_le le_rfl)
  have hle₂ : MeasurableSpace.comap (Prod.fst : Ω × B → Ω) mΩ ≤ by infer_instance :=
    hfst_meas.comap_le
  have hle₁ : MeasurableSpace.comap (Prod.snd : Ω × B → B) mB ≤ by infer_instance :=
    hsnd_meas.comap_le
  have key := condExp_indep_eq
    (m₁ := MeasurableSpace.comap (Prod.snd : Ω × B → B) mB)
    (m₂ := MeasurableSpace.comap (Prod.fst : Ω × B → Ω) mΩ)
    (μ := μ.prod ν) (f := fun ab : Ω × B => g ab.2)
    hle₁ hle₂ hf_meas hindep
  refine key.trans ?_
  have hint : ∫ ab : Ω × B, g ab.2 ∂(μ.prod ν) = ∫ b, g b ∂ν := by
    rw [integral_prod _ (hgi.comp_snd (μ := μ))]
    simp
  filter_upwards with x
  rw [hint]
