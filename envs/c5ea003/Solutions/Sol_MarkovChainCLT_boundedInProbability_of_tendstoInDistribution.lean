-- Prove2me | solution 1 for MarkovChainCLT.boundedInProbability_of_tendstoInDistribution
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T06:57:39.807202+00:00
-- url     : https://prove2.me/submissions/9030f1ea-bd46-4d45-ba83-a062cbe5fe85

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TightAux

/-- Every finite measure on `ℝ` has small tails. -/
lemma exists_tail_le (mu : Measure ℝ) [IsFiniteMeasure mu] {e : ℝ≥0∞} (he : 0 < e) :
    ∃ K : ℝ, mu {x : ℝ | K < |x|} ≤ e := by
  have hmeas : ∀ k : ℕ, NullMeasurableSet {x : ℝ | (k : ℝ) < |x|} mu := by
    intro k
    exact (measurableSet_lt measurable_const ((by fun_prop))).nullMeasurableSet
  have hmono : Antitone (fun k : ℕ => {x : ℝ | (k : ℝ) < |x|}) := by
    intro a b hab x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hab) hx
  have hinter : (⋂ k : ℕ, {x : ℝ | (k : ℝ) < |x|}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    obtain ⟨k, hk⟩ := exists_nat_gt |x|
    exact ⟨k, hk.le⟩
  have htend : Tendsto (fun k : ℕ => mu {x : ℝ | (k : ℝ) < |x|}) atTop
      (𝓝 (mu (⋂ k : ℕ, {x : ℝ | (k : ℝ) < |x|}))) :=
    tendsto_measure_iInter_atTop hmeas hmono ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at htend
  obtain ⟨k, hk⟩ := (htend.eventually (eventually_lt_nhds he)).exists
  exact ⟨(k : ℝ), hk.le⟩

end TightAux

/-- If a sequence of real random variables converges in distribution, then it is bounded in
probability (tight). -/
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℕ → Ω → ℝ) (W : Ω' → ℝ)
    (h : TendstoInDistribution Z atTop W (fun _ => P) P') :
    MarkovChainCLT.BoundedInProbability Z P := by
  intro eps heps
  set e : ℝ≥0∞ := ENNReal.ofReal eps with he_def
  have he : 0 < e := by simpa [he_def] using heps
  have hZm : ∀ n, AEMeasurable (Z n) P := h.forall_aemeasurable
  have habs : Measurable fun x : ℝ => |x| := (by fun_prop)
  -- the laws of `Z n` and of the limit
  have hlaw : ∀ n, IsProbabilityMeasure (P.map (Z n)) := fun n =>
    Measure.isProbabilityMeasure_map (hZm n)
  have hlimlaw : IsProbabilityMeasure (P'.map W) :=
    Measure.isProbabilityMeasure_map h.aemeasurable_limit
  -- tails of the limit law
  obtain ⟨R, hR⟩ := TightAux.exists_tail_le (P'.map W) (e := e / 2)
    (by simp [he.ne', ENNReal.div_pos_iff])
  set K₀ : ℝ := R + 1 with hK₀
  have hclosed : IsClosed {x : ℝ | K₀ ≤ |x|} :=
    isClosed_le continuous_const continuous_abs
  have hlimF : (P'.map W) {x : ℝ | K₀ ≤ |x|} ≤ e / 2 := by
    refine le_trans (measure_mono ?_) hR
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have : K₀ = R + 1 := hK₀
    linarith
  -- portmanteau
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hclosed
  have hlt : (atTop.limsup fun n => P.map (Z n) {x : ℝ | K₀ ≤ |x|}) < e := by
    refine lt_of_le_of_lt hport ?_
    exact lt_of_le_of_lt hlimF (ENNReal.half_lt_self he.ne' (by simp [he_def]))
  have hev : ∀ᶠ n in atTop, P.map (Z n) {x : ℝ | K₀ ≤ |x|} < e :=
    eventually_lt_of_limsup_lt hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- tails of each individual law
  have hEach : ∀ n : ℕ, ∃ K : ℝ, P.map (Z n) {x : ℝ | K < |x|} ≤ e := by
    intro n
    haveI : IsProbabilityMeasure (P.map (Z n)) := hlaw n
    exact TightAux.exists_tail_le _ he
  choose Kf hKf using hEach
  refine ⟨max K₀ (∑ n ∈ Finset.range N, |Kf n|), fun n => ?_⟩
  set K : ℝ := max K₀ (∑ n ∈ Finset.range N, |Kf n|) with hK
  have hsub : {ω | K < |Z n ω|} ⊆ Z n ⁻¹' {x : ℝ | K < |x|} := fun ω hω => hω
  have hmapeq : P.map (Z n) {x : ℝ | K < |x|} = P (Z n ⁻¹' {x : ℝ | K < |x|}) :=
    Measure.map_apply_of_aemeasurable (hZm n)
      (measurableSet_lt measurable_const habs)
  have hbound : P {ω | K < |Z n ω|} ≤ e := by
    by_cases hn : N ≤ n
    · have h1 : P.map (Z n) {x : ℝ | K < |x|} ≤ P.map (Z n) {x : ℝ | K₀ ≤ |x|} := by
        refine measure_mono ?_
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        have hKK : K₀ ≤ K := le_max_left _ _
        linarith
      have := (hN n hn).le
      calc P {ω | K < |Z n ω|} ≤ P (Z n ⁻¹' {x : ℝ | K < |x|}) := measure_mono hsub
        _ = P.map (Z n) {x : ℝ | K < |x|} := hmapeq.symm
        _ ≤ P.map (Z n) {x : ℝ | K₀ ≤ |x|} := h1
        _ ≤ e := this
    · have hn : n < N := lt_of_not_ge hn
      have hle : Kf n ≤ K := by
        refine le_trans (le_abs_self _) (le_trans ?_ (le_max_right K₀ _))
        exact Finset.single_le_sum (f := fun m => |Kf m|) (fun m _ => abs_nonneg _)
          (Finset.mem_range.mpr hn)
      have h1 : P.map (Z n) {x : ℝ | K < |x|} ≤ P.map (Z n) {x : ℝ | Kf n < |x|} :=
        measure_mono fun x hx => lt_of_le_of_lt hle hx
      calc P {ω | K < |Z n ω|} ≤ P (Z n ⁻¹' {x : ℝ | K < |x|}) := measure_mono hsub
        _ = P.map (Z n) {x : ℝ | K < |x|} := hmapeq.symm
        _ ≤ P.map (Z n) {x : ℝ | Kf n < |x|} := h1
        _ ≤ e := hKf n
  calc (P {ω | K < |Z n ω|}).toReal ≤ e.toReal :=
        ENNReal.toReal_mono (by simp [he_def]) hbound
    _ = eps := by simp [he_def, heps.le]
