-- Prove2me | solution 1 for BanditAlgorithm.ucb_suboptimal_arm_expected_pull_count_ceiling_bound
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-07-18T22:16:13.286675+00:00
-- url     : https://prove2.me/submissions/b211a818-efe3-4e77-a257-d018e62f6a16

import Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_good_event

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) ≤
      ((⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ : ℕ) : ℝ) +
        1 + 1 / (n : ℝ) := by
  let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
  obtain ⟨G, hG, hcap, hbad⟩ :=
    ucb_suboptimal_arm_good_event hk hν hn hπ i hi
  let μ := banditMeasure ν π n
  let bad : BanditHistory k n → ℝ := Gᶜ.indicator (fun _ ↦ 1)
  have hpull_eq (h : BanditHistory k n) :
      (armPullCount i h : ℝ) =
        ∑ t, if (h t).1 = i then (1 : ℝ) else 0 := by
    rw [armPullCount]
    have hset : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hset]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
        Finset.univ).symm
  have hpull_meas : AEMeasurable
      (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) μ := by
    have hcoord (t : Fin n) : Measurable
        (fun h : BanditHistory k n ↦ (h t).1) :=
      measurable_fst.comp (measurable_pi_apply t)
    have hind (t : Fin n) : Measurable
        (fun h : BanditHistory k n ↦ if (h t).1 = i then (1 : ℝ) else 0) :=
      Measurable.ite ((measurableSet_singleton i).preimage (hcoord t))
        measurable_const measurable_const
    have hsum : Measurable (fun h : BanditHistory k n ↦
        ∑ t, if (h t).1 = i then (1 : ℝ) else 0) := by
      exact Finset.measurable_sum _ fun t _ ↦ hind t
    exact hsum.aemeasurable.congr
      (Filter.Eventually.of_forall fun h ↦ (hpull_eq h).symm)
  have hT : Integrable
      (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) μ := by
    apply Integrable.of_mem_Icc 0 n
    · exact hpull_meas
    · filter_upwards [] with h
      constructor
      · positivity
      · have hcount : armPullCount i h ≤ n := by
          change ({t | (h t).1 = i}.toFinset : Finset (Fin n)).card ≤ n
          simpa using
            (Finset.card_le_univ
              ({t | (h t).1 = i}.toFinset : Finset (Fin n)))
        exact_mod_cast hcount
  have hbad_integrable : Integrable bad μ := by
    exact (integrable_const (1 : ℝ)).indicator hG.compl
  have hrhs : Integrable (fun h ↦ (u : ℝ) + n * bad h) μ :=
    (integrable_const (u : ℝ)).add (hbad_integrable.const_mul n)
  have h_expectation :
      ∫ h, (armPullCount i h : ℝ) ∂μ ≤
        (u : ℝ) + n * μ.real Gᶜ := by
    calc
      (∫ h, (armPullCount i h : ℝ) ∂μ) ≤
          ∫ h, ((u : ℝ) + n * bad h) ∂μ := by
        apply integral_mono hT hrhs
        intro h
        by_cases hh : h ∈ G
        · have hc : (armPullCount i h : ℝ) ≤ u := by
            exact_mod_cast hcap h hh
          simpa [bad, hh] using hc
        · have hc : (armPullCount i h : ℝ) ≤ n := by
            have hcount : armPullCount i h ≤ n := by
              change ({t | (h t).1 = i}.toFinset : Finset (Fin n)).card ≤ n
              simpa using
                (Finset.card_le_univ
                  ({t | (h t).1 = i}.toFinset : Finset (Fin n)))
            exact_mod_cast hcount
          have hu : (0 : ℝ) ≤ u := by positivity
          change (armPullCount i h : ℝ) ≤ (u : ℝ) + (n : ℝ) * bad h
          simp only [bad, Set.indicator_of_mem, Set.mem_compl_iff, hh,
            not_false_eq_true, mul_one]
          linarith
      _ = (u : ℝ) + n * μ.real Gᶜ := by
        have hbadIntegral : ∫ h, bad h ∂μ = μ.real Gᶜ := by
          simpa [bad] using (integral_indicator_one (μ := μ) hG.compl)
        rw [integral_add (integrable_const (u : ℝ))
          (hbad_integrable.const_mul n)]
        rw [integral_const, integral_const_mul, hbadIntegral]
        simp [μ]
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hscaled : (n : ℝ) * μ.real Gᶜ ≤ 1 + 1 / (n : ℝ) := by
    calc
      (n : ℝ) * μ.real Gᶜ ≤
          n * (1 / (n : ℝ) + 1 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbad (by positivity)
      _ = 1 + 1 / (n : ℝ) := by field_simp
  change (∫ h, (armPullCount i h : ℝ) ∂μ) ≤
    (u : ℝ) + 1 + 1 / (n : ℝ)
  linarith
