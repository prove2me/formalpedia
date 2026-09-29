-- Prove2me | solution 1 for MarkovChainCLT.tendsto_nat_mul_alphaMixingCoef_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T12:22:09.131533+00:00
-- url     : https://prove2.me/submissions/4e4be8af-92d1-49c5-ab56-d1dcc1f9b51c

import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_antitone
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- Abel–Pringsheim: a nonnegative, nonincreasing, summable sequence satisfies
`n * a n → 0`. -/
private theorem tendsto_nat_mul_of_antitone_of_summable' {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (hanti : Antitone a) (hsum : Summable a) :
    Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0) := by
  have key : ∀ n : ℕ, (n : ℝ) * a n ≤ 2 * ∑' k : ℕ, a (k + n / 2) := by
    intro n
    have hsub : ((n - n / 2 : ℕ) : ℝ) * a n ≤ ∑ k ∈ Finset.Ico (n / 2) n, a k := by
      have hmono : ∀ k ∈ Finset.Ico (n / 2) n, a n ≤ a k :=
        fun k hk => hanti (Finset.mem_Ico.1 hk).2.le
      calc ((n - n / 2 : ℕ) : ℝ)
            * a n = ∑ _k ∈ Finset.Ico (n / 2) n, a n := by
              rw [Finset.sum_const, Nat.card_Ico]
              simp [mul_comm]
        _ ≤ ∑ k ∈ Finset.Ico (n / 2) n, a k := Finset.sum_le_sum hmono
    have htail : ∑ k ∈ Finset.Ico (n / 2) n, a k ≤ ∑' k : ℕ, a (k + n / 2) := by
      have hs : Summable fun k : ℕ => a (k + n / 2) := hsum.comp_injective (add_left_injective _)
      have hmap : ∑ k ∈ Finset.Ico (n / 2) n, a k
          = ∑ k ∈ Finset.range (n - n / 2), a (k + n / 2) := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_eq_sum_range]
        simp [add_comm]
      rw [hmap]
      exact hs.sum_le_tsum _ fun k _ => ha0 _
    have hhalf : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
      have h : n ≤ 2 * (n - n / 2) := by omega
      exact_mod_cast h
    calc (n : ℝ) * a n ≤ (2 * ((n - n / 2 : ℕ) : ℝ)) * a n :=
          mul_le_mul_of_nonneg_right hhalf (ha0 n)
      _ = 2 * (((n - n / 2 : ℕ) : ℝ) * a n) := by ring
      _ ≤ 2 * ∑ k ∈ Finset.Ico (n / 2) n, a k := by linarith
      _ ≤ 2 * ∑' k : ℕ, a (k + n / 2) := by linarith
  have hzero : Tendsto (fun j : ℕ => ∑' k : ℕ, a (k + j)) atTop (𝓝 0) := tendsto_sum_nat_add a
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun n hn => by omega⟩
  have hcomp : Tendsto (fun n : ℕ => 2 * ∑' k : ℕ, a (k + n / 2)) atTop (𝓝 0) := by
    simpa using (hzero.comp hdiv).const_mul (2 : ℝ)
  exact squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg n) (ha0 n)) key hcomp

theorem solution {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (hα : Summable fun n => alphaMixingCoef P Y n) :
    Tendsto (fun n : ℕ => (n : ℝ) * alphaMixingCoef P Y n) atTop (𝓝 0) := by
  have hα_nonneg : ∀ n : ℕ, 0 ≤ alphaMixingCoef P Y n := by
    intro n
    refine le_csSup ⟨1, ?_⟩
      ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
        @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩
    rintro r ⟨k, A, B, -, -, rfl⟩
    have hAB1 : (P (A ∩ B)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ (A ∩ B)))
    have hA1 : (P A).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ A))
    have hB1 : (P B).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top P Set.univ)
        (measure_mono (Set.subset_univ B))
    have hA0 : (0 : ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
    have hB0 : (0 : ℝ) ≤ (P B).toReal := ENNReal.toReal_nonneg
    have hAB0 : (0 : ℝ) ≤ (P (A ∩ B)).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> nlinarith
  exact tendsto_nat_mul_of_antitone_of_summable' hα_nonneg
    (MarkovChainCLT.alphaMixingCoef_antitone P Y) hα
