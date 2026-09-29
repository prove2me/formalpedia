-- Prove2me | solution 1 for BanditAlgorithm.pmStochMeasure_kl_le_outside_selection
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T18:24:48.782549+00:00
-- url     : https://prove2.me/submissions/704aa369-0c8a-48f8-9dd1-27cd51581703

import Definitions.Def_PartialMonitoringStochastic
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

private lemma pmStochSnoc_measurableEmbedding
    {k n : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊] :
    MeasurableEmbedding
      (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) =>
        Fin.snoc (α := fun _ => Fin k × 𝕊) p.1 p.2) := by
  apply MeasurableEmbedding.of_measurable_inverse
    (g := fun h : PMHistory k 𝕊 (n + 1) => (Fin.init h, h (Fin.last n)))
    measurable_pmHistorySnoc
  · have hrange : Set.range
        (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) =>
          Fin.snoc (α := fun _ => Fin k × 𝕊) p.1 p.2) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro h
      exact ⟨(Fin.init h, h (Fin.last n)), Fin.snoc_init_self (q := h)⟩
    rw [hrange]
    exact MeasurableSet.univ
  · have hinit : Measurable (fun h : PMHistory k 𝕊 (n + 1) => Fin.init h) := by
      rw [measurable_pi_iff]
      intro s
      exact measurable_pi_apply _
    exact hinit.prodMk (measurable_pi_apply _)
  · intro p
    apply Prod.ext
    · exact Fin.init_snoc
        (α := fun _ : Fin (n + 1) => Fin k × 𝕊) (n := n) (p := p.1) (x := p.2)
    · exact Fin.snoc_last
        (α := fun _ : Fin (n + 1) => Fin k × 𝕊) (n := n) (p := p.1) (x := p.2)

private lemma pmSignalKernel_apply
    {k d : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (u : Fin d → ℝ)
    (hu : u ∈ stdSimplex ℝ (Fin d)) (c : Fin k) :
    pmSignalKernel G u hu c = pmSignalMeasure G u c := by
  rfl

private lemma pmStochStep_kl_eq_lintegral
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u v : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (hv : v ∈ stdSimplex ℝ (Fin d))
    (hfin : ∀ c, klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) ≠ ⊤)
    (h : PMHistory k 𝕊 n) :
    klDiv (pmStochStepKernel G π u hu n h)
        (pmStochStepKernel G π v hv n h) =
      ∫⁻ c, klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c)
        ∂π.select n h := by
  rw [pmStochStepKernel, pmStochStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  apply InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae
  filter_upwards [] with c
  simpa [Kernel.sectR_apply, pmSignalKernel_apply] using
    (klDiv_ne_top_iff.mp (hfin c)).1

private lemma pmStochStep_kl_ne_top
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u v : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (hv : v ∈ stdSimplex ℝ (Fin d))
    (hfin : ∀ c, klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) ≠ ⊤)
    (h : PMHistory k 𝕊 n) :
    klDiv (pmStochStepKernel G π u hu n h)
        (pmStochStepKernel G π v hv n h) ≠ ⊤ := by
  rw [pmStochStep_kl_eq_lintegral G π u v hu hv hfin h, lintegral_fintype]
  rw [ENNReal.sum_ne_top]
  intro c hc
  exact ENNReal.mul_ne_top (hfin c) (by simp)

private lemma pmStochMeasure_succ_chain
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u v : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (hv : v ∈ stdSimplex ℝ (Fin d)) :
    klDiv (pmStochMeasure G π u hu (n + 1)) (pmStochMeasure G π v hv (n + 1)) =
      klDiv (pmStochMeasure G π u hu n) (pmStochMeasure G π v hv n) +
        klDiv
          ((pmStochMeasure G π u hu n).compProd (pmStochStepKernel G π u hu n))
          ((pmStochMeasure G π u hu n).compProd (pmStochStepKernel G π v hv n)) := by
  rw [pmStochMeasure, pmStochMeasure]
  rw [InformationTheory.klDiv_map_measurableEmbedding pmStochSnoc_measurableEmbedding]
  exact InformationTheory.klDiv_compProd_eq_add _ _ _ _

end BanditAlgorithm

open BanditAlgorithm

/-- Adaptive KL bound for stochastic partial monitoring.  If the two feedback
laws agree on `N` and every action outside `N` has one-step KL at most `B`,
then history KL is bounded by `B` times the expected outside-selection mass.
This is the inequality form of Lattimore--Szepesvari Eq. (37.8), p.490. -/
theorem solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u v : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (hv : v ∈ stdSimplex ℝ (Fin d)) (N : Finset (Fin k)) (B : ℝ≥0∞)
    (hfin : ∀ c, klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) ≠ ⊤)
    (heq : ∀ c, c ∈ N → pmSignalMeasure G u c = pmSignalMeasure G v c)
    (hle : ∀ c, c ∉ N → klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) ≤ B) :
    ∀ n : ℕ,
      klDiv (pmStochMeasure G π u hu n) (pmStochMeasure G π v hv n) ≤
        B * ∑ t ∈ Finset.range n,
          ∫⁻ h, ∑ c ∈ Finset.univ.filter (fun c => c ∉ N),
            (π.select t h) {c} ∂pmStochMeasure G π u hu t := by
  classical
  letI (c : Fin k) : IsProbabilityMeasure (pmSignalMeasure G u c) :=
    pmSignalMeasure_isProbabilityMeasure G u hu c
  letI (c : Fin k) : IsProbabilityMeasure (pmSignalMeasure G v c) :=
    pmSignalMeasure_isProbabilityMeasure G v hv c
  intro n
  induction n with
  | zero => simp [pmStochMeasure]
  | succ n ih =>
      rw [pmStochMeasure_succ_chain G π u v hu hv]
      have hstep_ac : ∀ᵐ h ∂pmStochMeasure G π u hu n,
          pmStochStepKernel G π u hu n h ≪ pmStochStepKernel G π v hv n h := by
        filter_upwards [] with h
        exact (klDiv_ne_top_iff.mp
          (pmStochStep_kl_ne_top G π u v hu hv hfin h)).1
      rw [InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae
        (pmStochMeasure G π u hu n)
        (pmStochStepKernel G π u hu n)
        (pmStochStepKernel G π v hv n) hstep_ac]
      have hpoint : ∀ h : PMHistory k 𝕊 n,
          klDiv (pmStochStepKernel G π u hu n h)
              (pmStochStepKernel G π v hv n h) ≤
            B * ∑ c ∈ Finset.univ.filter (fun c => c ∉ N), (π.select n h) {c} := by
        intro h
        rw [pmStochStep_kl_eq_lintegral G π u v hu hv hfin h, lintegral_fintype]
        calc
          (∑ c, klDiv (pmSignalMeasure G u c) (pmSignalMeasure G v c) *
              (π.select n h) {c}) ≤
              ∑ c, (if c ∈ N then 0 else B) *
                (π.select n h) {c} := by
            apply Finset.sum_le_sum
            intro c hc
            by_cases hcN : c ∈ N
            · simp only [hcN, if_pos, zero_mul]
              rw [heq c hcN, klDiv_self, zero_mul]
            · simp only [hcN, if_neg]
              exact mul_le_mul_right' (hle c hcN) _
          _ = B * ∑ c ∈ Finset.univ.filter (fun c => c ∉ N),
                (π.select n h) {c} := by
            rw [Finset.mul_sum]
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro c hc
            by_cases hcN : c ∈ N <;> simp [hcN]
      have hmeas : Measurable (fun h : PMHistory k 𝕊 n =>
          ∑ c ∈ Finset.univ.filter (fun c => c ∉ N), (π.select n h) {c}) := by
        let s := Finset.univ.filter (fun c => c ∉ N)
        change Measurable (fun h : PMHistory k 𝕊 n => ∑ c ∈ s, (π.select n h) {c})
        induction s using Finset.induction_on with
        | empty => simp
        | @insert c s hc ih =>
            simp only [Finset.sum_insert hc]
            exact (Kernel.measurable_coe (π.select n) (MeasurableSet.singleton c)).add ih
      calc
        klDiv (pmStochMeasure G π u hu n) (pmStochMeasure G π v hv n) +
            ∫⁻ h, klDiv (pmStochStepKernel G π u hu n h)
              (pmStochStepKernel G π v hv n h) ∂pmStochMeasure G π u hu n ≤
            B * ∑ t ∈ Finset.range n,
              ∫⁻ h, ∑ c ∈ Finset.univ.filter (fun c => c ∉ N),
                (π.select t h) {c} ∂pmStochMeasure G π u hu t +
            ∫⁻ h, B * ∑ c ∈ Finset.univ.filter (fun c => c ∉ N),
              (π.select n h) {c} ∂pmStochMeasure G π u hu n :=
          add_le_add ih (lintegral_mono hpoint)
        _ = B * ∑ t ∈ Finset.range (n + 1),
              ∫⁻ h, ∑ c ∈ Finset.univ.filter (fun c => c ∉ N),
                (π.select t h) {c} ∂pmStochMeasure G π u hu t := by
          rw [lintegral_const_mul _ hmeas, Finset.sum_range_succ]
          rw [mul_add]
