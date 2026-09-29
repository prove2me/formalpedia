-- Prove2me | solution 1 for measure_Ici_toReal_continuous_of_atomless
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T01:39:38.420378+00:00
-- url     : https://prove2.me/submissions/02504f82-b893-406e-bd6d-75cf2946daa0

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

namespace TailContAux

/-- The shrinking open intervals around `p` intersect in `{p}`. -/
lemma iInter_Ioo_eq_singleton (p : ℝ) :
    (⋂ n : ℕ, Ioo (p - 1 / ((n : ℝ) + 1)) (p + 1 / ((n : ℝ) + 1))) = {p} := by
  ext x
  simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr (sub_ne_zero.mpr hne))
    have h := hx n
    have habs : |x - p| < 1 / ((n : ℝ) + 1) :=
      abs_sub_lt_iff.mpr ⟨by linarith [h.2], by linarith [h.1]⟩
    linarith
  · rintro rfl n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨by linarith, by linarith⟩

/-- The measure of the shrinking intervals around an atomless point tends to `0`
(after `toReal`). -/
lemma tendsto_toReal_measure_Ioo (ν : Measure ℝ) [IsFiniteMeasure ν] (p : ℝ)
    (hatom : ν {p} = 0) :
    Filter.Tendsto
      (fun n : ℕ => (ν (Ioo (p - 1 / ((n : ℝ) + 1)) (p + 1 / ((n : ℝ) + 1)))).toReal)
      Filter.atTop (nhds 0) := by
  have hanti : Antitone fun n : ℕ => Ioo (p - 1 / ((n : ℝ) + 1)) (p + 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by exact_mod_cast Nat.succ_le_succ hmn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le h1 h2
    exact Ioo_subset_Ioo (by linarith) (by linarith)
  have htend := tendsto_measure_iInter_atTop (μ := ν)
    (s := fun n : ℕ => Ioo (p - 1 / ((n : ℝ) + 1)) (p + 1 / ((n : ℝ) + 1)))
    (fun _ => measurableSet_Ioo.nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
  rw [iInter_Ioo_eq_singleton p, hatom] at htend
  have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp htend
  simpa [Function.comp] using h

/-- If `|x - p| < δ` then the difference of the tails at `x` and `p` is bounded
by the measure of `(p - δ, p + δ)`. -/
lemma abs_tail_sub_le (ν : Measure ℝ) [IsFiniteMeasure ν] {p x δ : ℝ}
    (hx : |x - p| < δ) :
    |(ν (Ici x)).toReal - (ν (Ici p)).toReal| ≤ (ν (Ioo (p - δ) (p + δ))).toReal := by
  have habs := abs_sub_lt_iff.mp hx
  rcases lt_trichotomy x p with hlt | heq | hgt
  · -- `x < p`: `Ici x = Ico x p ∪ Ici p`
    have hsub : Ico x p ⊆ Ioo (p - δ) (p + δ) := by
      intro v hv
      rw [mem_Ico] at hv
      rw [mem_Ioo]
      constructor <;> linarith [habs.1, habs.2, hv.1, hv.2]
    have hdisj : Disjoint (Ico x p) (Ici p) := by
      rw [Set.disjoint_left]
      intro v hv hv'
      rw [mem_Ico] at hv
      rw [mem_Ici] at hv'
      linarith [hv.2]
    have hm : ν (Ici x) = ν (Ico x p) + ν (Ici p) := by
      rw [← Ico_union_Ici_eq_Ici hlt.le, measure_union hdisj measurableSet_Ici]
    have hTx : (ν (Ici x)).toReal = (ν (Ico x p)).toReal + (ν (Ici p)).toReal := by
      rw [hm, ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
    have hb : (ν (Ico x p)).toReal ≤ (ν (Ioo (p - δ) (p + δ))).toReal :=
      ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsub)
    rw [hTx, add_sub_cancel_right, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hb
  · rw [heq, sub_self, abs_zero]
    exact ENNReal.toReal_nonneg
  · -- `p < x`: `Ici p = Ico p x ∪ Ici x`
    have hsub : Ico p x ⊆ Ioo (p - δ) (p + δ) := by
      intro v hv
      rw [mem_Ico] at hv
      rw [mem_Ioo]
      constructor <;> linarith [habs.1, habs.2, hv.1, hv.2]
    have hdisj : Disjoint (Ico p x) (Ici x) := by
      rw [Set.disjoint_left]
      intro v hv hv'
      rw [mem_Ico] at hv
      rw [mem_Ici] at hv'
      linarith [hv.2]
    have hm : ν (Ici p) = ν (Ico p x) + ν (Ici x) := by
      rw [← Ico_union_Ici_eq_Ici hgt.le, measure_union hdisj measurableSet_Ici]
    have hTp : (ν (Ici p)).toReal = (ν (Ico p x)).toReal + (ν (Ici x)).toReal := by
      rw [hm, ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
    have hb : (ν (Ico p x)).toReal ≤ (ν (Ioo (p - δ) (p + δ))).toReal :=
      ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsub)
    rw [hTp]
    have hswap : (ν (Ici x)).toReal - ((ν (Ico p x)).toReal + (ν (Ici x)).toReal)
        = -((ν (Ico p x)).toReal) := by ring
    rw [hswap, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hb

end TailContAux

theorem solution
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hatom : ∀ p : ℝ, ν {p} = 0) :
    Continuous fun p : ℝ => (ν (Ici p)).toReal := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ :=
    ((TailContAux.tendsto_toReal_measure_Ioo ν p (hatom p)).eventually (gt_mem_nhds hε)).exists
  have hδpos : (0 : ℝ) < 1 / ((n₀ : ℝ) + 1) := by positivity
  refine ⟨1 / ((n₀ : ℝ) + 1), hδpos, ?_⟩
  intro x hx
  rw [Real.dist_eq] at hx
  rw [Real.dist_eq]
  calc |(ν (Ici x)).toReal - (ν (Ici p)).toReal|
      ≤ (ν (Ioo (p - 1 / ((n₀ : ℝ) + 1)) (p + 1 / ((n₀ : ℝ) + 1)))).toReal :=
        TailContAux.abs_tail_sub_le ν hx
    _ < ε := hn₀
