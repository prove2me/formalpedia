-- Prove2me | solution 1 for InformationTheory.klDiv_restrict_add_klDiv_restrict_compl
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T15:39:15.785029+00:00
-- url     : https://prove2.me/submissions/09382ba7-531a-484c-93e6-e8933ed7cdf9

import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Additivity of the Kullback-Leibler divergence over a measurable partition

`klDiv μ ν = klDiv (μ|_s) (ν|_s) + klDiv (μ|_sᶜ) (ν|_sᶜ)`.

This is the "localisation" step behind L&S Exercise 14.13 (printed p. 197): to compare the
divergences carried by two nested σ-algebras one splits the space along an event of the
smaller σ-algebra and compares the two halves separately.

Mathlib defines `klDiv μ ν = ENNReal.ofReal (∫ llr μ ν ∂μ + ν univ - μ univ)` (the
mass-corrected form), which is exactly what makes the divergence additive over a partition
for *finite*, not merely probability, measures.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α}

namespace InformationTheory

/-- If `μ ≪ ν`, the restriction of `μ` to `s` is the restriction of `ν` weighted by `dμ/dν`. -/
lemma restrict_eq_withDensity_rnDeriv (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (s : Set α) :
    μ.restrict s = (ν.restrict s).withDensity (μ.rnDeriv ν) := by
  ext A hA
  rw [withDensity_apply _ hA, Measure.restrict_restrict hA, Measure.restrict_apply hA,
    Measure.setLIntegral_rnDeriv hμν]

/-- On `s`, the log-likelihood ratio of the restricted measures agrees with the original one. -/
lemma llr_restrict_ae (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (s : Set α) :
    llr (μ.restrict s) (ν.restrict s) =ᵐ[μ.restrict s] llr μ ν := by
  have hrn : (μ.restrict s).rnDeriv (ν.restrict s) =ᵐ[ν.restrict s] μ.rnDeriv ν := by
    rw [restrict_eq_withDensity_rnDeriv μ ν hμν s]
    exact Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv μ ν)
  have hac : μ.restrict s ≪ ν.restrict s := hμν.restrict s
  filter_upwards [hac hrn] with x hx
  simp only [llr_def, hx]

/-- The `klDiv` of a restricted pair, written with the original log-likelihood ratio. -/
lemma klDiv_restrict_eq (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (s : Set α) (hint : IntegrableOn (llr μ ν) s μ) :
    klDiv (μ.restrict s) (ν.restrict s) =
      ENNReal.ofReal (∫ x in s, llr μ ν x ∂μ + ν.real s - μ.real s) := by
  have hac : μ.restrict s ≪ ν.restrict s := hμν.restrict s
  have hcongr := llr_restrict_ae μ ν hμν s
  have hint' : Integrable (llr (μ.restrict s) (ν.restrict s)) (μ.restrict s) :=
    hint.congr hcongr.symm
  rw [klDiv_of_ac_of_integrable hac hint', integral_congr_ae hcongr]
  simp [measureReal_def, Measure.restrict_apply_univ]

end InformationTheory

theorem solution (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) :
    klDiv μ ν = klDiv (μ.restrict s) (ν.restrict s) + klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) := by
  classical
  by_cases hμν : μ ≪ ν
  swap
  · -- Not absolutely continuous: both sides are `⊤`.
    rw [klDiv_of_not_ac hμν]
    have hnot : ¬ (μ.restrict s ≪ ν.restrict s ∧ μ.restrict sᶜ ≪ ν.restrict sᶜ) := by
      rintro ⟨h1, h2⟩
      refine hμν (Measure.AbsolutelyContinuous.mk fun A hA hνA ↦ ?_)
      have e1 : μ.restrict s A = 0 := h1 (by
        rw [Measure.restrict_apply hA]
        exact measure_mono_null inter_subset_left hνA)
      have e2 : μ.restrict sᶜ A = 0 := h2 (by
        rw [Measure.restrict_apply hA]
        exact measure_mono_null inter_subset_left hνA)
      rw [Measure.restrict_apply hA] at e1 e2
      have hsplit : μ (A ∩ s) + μ (A \ s) = μ A := measure_inter_add_diff (μ := μ) A hs
      rw [Set.diff_eq, e1, e2, zero_add] at hsplit
      exact hsplit.symm
    rcases not_and_or.mp hnot with h | h
    · rw [klDiv_of_not_ac h]; simp
    · rw [klDiv_of_not_ac h]; simp
  · by_cases hint : Integrable (llr μ ν) μ
    swap
    · -- Not integrable: the left side is `⊤`, and integrability on both halves would
      -- reassemble to integrability on the whole space.
      rw [klDiv_of_not_integrable hint]
      have hnot : klDiv (μ.restrict s) (ν.restrict s) = ⊤ ∨
          klDiv (μ.restrict sᶜ) (ν.restrict sᶜ) = ⊤ := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨h1, h2⟩ := hcon
        have i1 := (klDiv_ne_top_iff.mp h1).2
        have i2 := (klDiv_ne_top_iff.mp h2).2
        have j1 : IntegrableOn (llr μ ν) s μ :=
          i1.congr (llr_restrict_ae μ ν hμν s)
        have j2 : IntegrableOn (llr μ ν) sᶜ μ :=
          i2.congr (llr_restrict_ae μ ν hμν sᶜ)
        have : IntegrableOn (llr μ ν) (s ∪ sᶜ) μ := j1.union j2
        rw [Set.union_compl_self, integrableOn_univ] at this
        exact hint this
      rcases hnot with h | h
      · rw [h]; simp
      · rw [h]; simp
    · -- Main case: split the integral and the masses along `s`.
      have j1 : IntegrableOn (llr μ ν) s μ := hint.integrableOn
      have j2 : IntegrableOn (llr μ ν) sᶜ μ := hint.integrableOn
      have hA : 0 ≤ ∫ x in s, llr μ ν x ∂μ + ν.real s - μ.real s := by
        have := integral_llr_add_sub_measure_univ_nonneg (hμν.restrict s)
          ((j1.congr (llr_restrict_ae μ ν hμν s).symm))
        rwa [integral_congr_ae (llr_restrict_ae μ ν hμν s),
          show (ν.restrict s).real univ = ν.real s by
            simp [measureReal_def, Measure.restrict_apply_univ],
          show (μ.restrict s).real univ = μ.real s by
            simp [measureReal_def, Measure.restrict_apply_univ]] at this
      have hB : 0 ≤ ∫ x in sᶜ, llr μ ν x ∂μ + ν.real sᶜ - μ.real sᶜ := by
        have := integral_llr_add_sub_measure_univ_nonneg (hμν.restrict sᶜ)
          ((j2.congr (llr_restrict_ae μ ν hμν sᶜ).symm))
        rwa [integral_congr_ae (llr_restrict_ae μ ν hμν sᶜ),
          show (ν.restrict sᶜ).real univ = ν.real sᶜ by
            simp [measureReal_def, Measure.restrict_apply_univ],
          show (μ.restrict sᶜ).real univ = μ.real sᶜ by
            simp [measureReal_def, Measure.restrict_apply_univ]] at this
      rw [klDiv_of_ac_of_integrable hμν hint,
        klDiv_restrict_eq μ ν hμν s j1, klDiv_restrict_eq μ ν hμν sᶜ j2,
        ← ENNReal.ofReal_add hA hB]
      congr 1
      have hsplit : ∫ x in s, llr μ ν x ∂μ + ∫ x in sᶜ, llr μ ν x ∂μ = ∫ x, llr μ ν x ∂μ :=
        integral_add_compl hs hint
      have hν : ν.real s + ν.real sᶜ = ν.real univ :=
        measureReal_add_measureReal_compl (μ := ν) hs
      have hμ : μ.real s + μ.real sᶜ = μ.real univ :=
        measureReal_add_measureReal_compl (μ := μ) hs
      linarith [hsplit, hν, hμ]
