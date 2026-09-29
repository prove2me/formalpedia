-- Prove2me | solution 1 for BanditAlgorithm.pmSignalMeasure_kl_le_symmetric_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T18:41:12.320497+00:00
-- url     : https://prove2.me/submissions/6ec4e8ab-de4a-4c46-a964-c84a2b5761eb

import Definitions.Def_PartialMonitoringStochastic
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Theorems.Thm_InformationTheory_klDiv_map_eq_klDiv_trim_comap
import Theorems.Thm_InformationTheory_klDiv_trim_le_of_isFiniteMeasure

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

private lemma pmOutcomeMeasure_real_singleton {d : ℕ}
    (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) (j : Fin d) :
    (pmOutcomeMeasure u).real {j} = u j := by
  rw [Measure.real, pmOutcomeMeasure,
    Measure.sum_apply _ (MeasurableSet.singleton j)]
  simp only [
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator, Set.mem_singleton_iff, Pi.one_apply, tsum_fintype]
  rw [Finset.sum_eq_single j]
  · simp [hu j]
  · intro b _ hbj
    simp [hbj]
  · simp

end BanditAlgorithm

namespace InformationTheory

private theorem symmetric_perturbation_kl_sum_le
    {d : ℕ} (u q : Fin d → ℝ) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ δ / 2)
    (hmargin : ∀ i, δ * |q i| ≤ u i)
    (hqsum : ∑ i, q i = 0) :
    ∑ i, (u i - Δ * q i) *
        Real.log ((u i - Δ * q i) / (u i + Δ * q i)) ≤
      (8 * Δ ^ 2 / δ) * ∑ i, |q i| := by
  have hpoint : ∀ i : Fin d,
      (u i - Δ * q i) *
          Real.log ((u i - Δ * q i) / (u i + Δ * q i)) ≤
        (u i - Δ * q i - (u i + Δ * q i)) +
          (8 * Δ ^ 2 / δ) * |q i| := by
    intro i
    by_cases hqi : q i = 0
    · simp [hqi]
    have habs : 0 < |q i| := abs_pos.mpr hqi
    have hδabs : 0 < δ * |q i| := mul_pos hδ habs
    have hu : 0 < u i := lt_of_lt_of_le hδabs (hmargin i)
    have hΔabs : Δ * |q i| ≤ (δ / 2) * |q i| :=
      mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)
    have hp : 0 < u i - Δ * q i := by
      have hqle : q i ≤ |q i| := le_abs_self _
      have hmul : Δ * q i ≤ Δ * |q i| :=
        mul_le_mul_of_nonneg_left hqle hΔ0
      have hhalf : (δ / 2) * |q i| < u i := by
        nlinarith [hδabs, hmargin i]
      linarith
    have hr : 0 < u i + Δ * q i := by
      have hnegqle : -q i ≤ |q i| := neg_le_abs _
      have hmul : -(Δ * q i) ≤ Δ * |q i| := by
        calc
          -(Δ * q i) = Δ * (-q i) := by ring
          _ ≤ Δ * |q i| := mul_le_mul_of_nonneg_left hnegqle hΔ0
      have hhalf : (δ / 2) * |q i| < u i := by
        nlinarith [hδabs, hmargin i]
      linarith
    have hlog := Real.log_le_sub_one_of_pos (div_pos hp hr)
    have hmul := mul_le_mul_of_nonneg_left hlog hp.le
    have hr_lower : (δ / 2) * |q i| ≤ u i + Δ * q i := by
      have hnegqle : -q i ≤ |q i| := neg_le_abs _
      have hmul' : -(Δ * q i) ≤ Δ * |q i| := by
        calc
          -(Δ * q i) = Δ * (-q i) := by ring
          _ ≤ Δ * |q i| := mul_le_mul_of_nonneg_left hnegqle hΔ0
      linarith [hmargin i, hΔabs]
    have hsquare :
        (u i - Δ * q i - (u i + Δ * q i)) ^ 2 /
            (u i + Δ * q i) ≤
          (8 * Δ ^ 2 / δ) * |q i| := by
      rw [div_le_iff₀ hr]
      have hδne : δ ≠ 0 := ne_of_gt hδ
      have habsne : |q i| ≠ 0 := ne_of_gt habs
      calc
        (u i - Δ * q i - (u i + Δ * q i)) ^ 2 =
            4 * Δ ^ 2 * |q i| ^ 2 := by rw [sq_abs (q i)]; ring
        _ ≤ ((8 * Δ ^ 2 / δ) * |q i|) *
              (u i + Δ * q i) := by
            have hcoef : 0 ≤ (8 * Δ ^ 2 / δ) * |q i| := by positivity
            calc
              4 * Δ ^ 2 * |q i| ^ 2 =
                  ((8 * Δ ^ 2 / δ) * |q i|) *
                    ((δ / 2) * |q i|) := by field_simp; ring
              _ ≤ ((8 * Δ ^ 2 / δ) * |q i|) *
                    (u i + Δ * q i) :=
                mul_le_mul_of_nonneg_left hr_lower hcoef
    calc
      (u i - Δ * q i) *
          Real.log ((u i - Δ * q i) / (u i + Δ * q i)) ≤
          (u i - Δ * q i) *
            ((u i - Δ * q i) / (u i + Δ * q i) - 1) := hmul
      _ = (u i - Δ * q i - (u i + Δ * q i)) +
          (u i - Δ * q i - (u i + Δ * q i)) ^ 2 /
            (u i + Δ * q i) := by field_simp; ring
      _ ≤ (u i - Δ * q i - (u i + Δ * q i)) +
          (8 * Δ ^ 2 / δ) * |q i| := by gcongr
  calc
    ∑ i, (u i - Δ * q i) *
        Real.log ((u i - Δ * q i) / (u i + Δ * q i)) ≤
        ∑ i, ((u i - Δ * q i - (u i + Δ * q i)) +
          (8 * Δ ^ 2 / δ) * |q i|) := Finset.sum_le_sum fun i _ => hpoint i
    _ = (8 * Δ ^ 2 / δ) * ∑ i, |q i| := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hz : ∑ i, (u i - Δ * q i - (u i + Δ * q i)) = 0 := by
        calc
          ∑ i, (u i - Δ * q i - (u i + Δ * q i)) =
              -2 * Δ * ∑ i, q i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
          _ = 0 := by rw [hqsum]; ring
      rw [hz, zero_add]

end InformationTheory

namespace BanditAlgorithm

private theorem pmOutcomeMeasure_kl_le_symmetric_perturbation
    {d : ℕ} [NeZero d] (u q : Fin d → ℝ) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ δ / 2)
    (hmargin : ∀ i, δ * |q i| ≤ u i)
    (hqsum : ∑ i, q i = 0) (humass : ∑ i, u i = 1) :
    klDiv (pmOutcomeMeasure (fun i => u i - Δ * q i))
        (pmOutcomeMeasure (fun i => u i + Δ * q i)) ≤
      ENNReal.ofReal ((8 * Δ ^ 2 / δ) * ∑ i, |q i|) := by
  let p : Fin d → ℝ := fun i => u i - Δ * q i
  let r : Fin d → ℝ := fun i => u i + Δ * q i
  have hΔabs : ∀ i, Δ * |q i| ≤ (δ / 2) * |q i| := fun i =>
    mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    have hmul : Δ * q i ≤ Δ * |q i| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hΔ0
    dsimp [p]
    nlinarith [hmargin i, hΔabs i, mul_nonneg hδ.le (abs_nonneg (q i))]
  have hr0 : ∀ i, 0 ≤ r i := by
    intro i
    have hmul : -(Δ * q i) ≤ Δ * |q i| := by
      calc
        -(Δ * q i) = Δ * (-q i) := by ring
        _ ≤ Δ * |q i| :=
          mul_le_mul_of_nonneg_left (neg_le_abs _) hΔ0
    dsimp [r]
    nlinarith [hmargin i, hΔabs i, mul_nonneg hδ.le (abs_nonneg (q i))]
  have hpr : ∀ i, p i ≤ 3 * r i := by
    intro i
    have hpupper : p i ≤ u i + Δ * |q i| := by
      dsimp [p]
      have := mul_le_mul_of_nonneg_left (neg_le_abs (q i)) hΔ0
      nlinarith
    have hrlower : u i - Δ * |q i| ≤ r i := by
      dsimp [r]
      have := mul_le_mul_of_nonneg_left (neg_le_abs (q i)) hΔ0
      nlinarith
    nlinarith [hmargin i, hΔabs i]
  have hpsum : ∑ i, p i = 1 := by
    dsimp [p]
    calc
      ∑ i, (u i - Δ * q i) = ∑ i, u i - Δ * ∑ i, q i := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = ∑ i, u i := by rw [hqsum]; ring
      _ = 1 := humass
  have hrsum : ∑ i, r i = 1 := by
    dsimp [r]
    calc
      ∑ i, (u i + Δ * q i) = ∑ i, u i + Δ * ∑ i, q i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 1 := by rw [hqsum, humass]; ring
  have hpSimplex : p ∈ stdSimplex ℝ (Fin d) := ⟨hp0, hpsum⟩
  have hrSimplex : r ∈ stdSimplex ℝ (Fin d) := ⟨hr0, hrsum⟩
  letI : IsProbabilityMeasure (pmOutcomeMeasure p) :=
    pmOutcomeMeasure_isProbabilityMeasure p hpSimplex
  letI : IsProbabilityMeasure (pmOutcomeMeasure r) :=
    pmOutcomeMeasure_isProbabilityMeasure r hrSimplex
  have hac : pmOutcomeMeasure p ≪ pmOutcomeMeasure r := by
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hzero
    rw [pmOutcomeMeasure, Measure.sum_apply _ hs] at hzero ⊢
    apply ENNReal.tsum_eq_zero.mpr
    intro i
    have hi := ENNReal.tsum_eq_zero.mp hzero i
    simp only [Measure.smul_apply, smul_eq_mul] at hi ⊢
    by_cases his : i ∈ s
    · simp [Measure.dirac_apply, his] at hi ⊢
      exact (hpr i).trans
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hi)
    · simp [Measure.dirac_apply, his]
  have hfin : klDiv (pmOutcomeMeasure p) (pmOutcomeMeasure r) ≠ ⊤ :=
    klDiv_ne_top_iff.mpr ⟨hac, Integrable.of_finite⟩
  apply (ENNReal.toReal_le_toReal hfin (by simp)).mp
  rw [InformationTheory.categorical_toReal_klDiv_eq_sum
    (pmOutcomeMeasure p) (pmOutcomeMeasure r) hac]
  simp_rw [pmOutcomeMeasure_real_singleton p hp0,
    pmOutcomeMeasure_real_singleton r hr0]
  rw [ENNReal.toReal_ofReal]
  · exact InformationTheory.symmetric_perturbation_kl_sum_le
      u q hδ hΔ0 hΔ hmargin hqsum
  · positivity

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊] [NeZero d]
    (G : PartialMonitoringGame k d 𝕊) (c : Fin k)
    (u q : Fin d → ℝ) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ δ / 2)
    (hmargin : ∀ i, δ * |q i| ≤ u i)
    (hqsum : ∑ i, q i = 0) (humass : ∑ i, u i = 1) :
    klDiv (pmSignalMeasure G (fun i => u i - Δ * q i) c)
        (pmSignalMeasure G (fun i => u i + Δ * q i) c) ≤
      ENNReal.ofReal ((8 * Δ ^ 2 / δ) * ∑ i, |q i|) := by
  have hΔabs : ∀ i, Δ * |q i| ≤ (δ / 2) * |q i| := fun i =>
    mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)
  have hp0 : ∀ i, 0 ≤ u i - Δ * q i := by
    intro i
    have hmul : Δ * q i ≤ Δ * |q i| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hΔ0
    nlinarith [hmargin i, hΔabs i, mul_nonneg hδ.le (abs_nonneg (q i))]
  have hr0 : ∀ i, 0 ≤ u i + Δ * q i := by
    intro i
    have hmul : -(Δ * q i) ≤ Δ * |q i| := by
      calc
        -(Δ * q i) = Δ * (-q i) := by ring
        _ ≤ Δ * |q i| :=
          mul_le_mul_of_nonneg_left (neg_le_abs _) hΔ0
    nlinarith [hmargin i, hΔabs i, mul_nonneg hδ.le (abs_nonneg (q i))]
  have hpsum : ∑ i, (u i - Δ * q i) = 1 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hqsum, humass]
    ring
  have hrsum : ∑ i, (u i + Δ * q i) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hqsum, humass]
    ring
  letI : IsProbabilityMeasure
      (pmOutcomeMeasure (fun i => u i - Δ * q i)) :=
    pmOutcomeMeasure_isProbabilityMeasure _ ⟨hp0, hpsum⟩
  letI : IsProbabilityMeasure
      (pmOutcomeMeasure (fun i => u i + Δ * q i)) :=
    pmOutcomeMeasure_isProbabilityMeasure _ ⟨hr0, hrsum⟩
  rw [pmSignalMeasure, pmSignalMeasure,
    InformationTheory.klDiv_map_eq_klDiv_trim_comap
      (measurable_of_countable (G.Φ c))]
  exact (InformationTheory.klDiv_trim_le_of_isFiniteMeasure
    (measurable_of_countable (G.Φ c)).comap_le
    (pmOutcomeMeasure (fun i => u i - Δ * q i))
    (pmOutcomeMeasure (fun i => u i + Δ * q i))).trans
      (pmOutcomeMeasure_kl_le_symmetric_perturbation
        u q hδ hΔ0 hΔ hmargin hqsum humass)

end BanditAlgorithm
