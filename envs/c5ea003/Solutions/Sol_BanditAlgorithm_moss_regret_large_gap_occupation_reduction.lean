-- Prove2me | solution 1 for BanditAlgorithm.moss_regret_large_gap_occupation_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-07-29T01:59:06.851929+00:00
-- url     : https://prove2.me/submissions/f351da4d-8219-4de8-abd4-9ded8b10240b

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_bandit_canonical_occupation_identities
import Definitions.Def_banditRegret
import Definitions.Def_mossPolicy

open MeasureTheory ProbabilityTheory BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsMOSSPolicy n π) (hkn : k ≤ n) :
    BanditAlgorithm.banditRegret ν π n ≤
      24 * Real.sqrt ((k : ℝ) * n) +
        Finset.sum
          (Finset.univ.filter
            (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < BanditAlgorithm.banditGap ν i))
          (fun i ↦ BanditAlgorithm.banditGap ν i *
            MeasureTheory.integral
              (BanditAlgorithm.banditMeasure ν π n)
              (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ))) := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set E : Fin k → ℝ :=
    fun i ↦ ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) with hE
  -- every expected occupation count is nonnegative
  have hEnonneg : ∀ i, 0 ≤ E i := by
    intro i
    exact integral_nonneg (fun h ↦ by positivity)
  -- the occupation counts sum to the horizon
  have hsum : (∑ i, E i) = (n : ℝ) :=
    (bandit_canonical_occupation_identities ν hν.1 π n).2
  -- regret decomposition (L&S Lemma 4.5)
  have hdec : banditRegret ν π n = ∑ i, banditGap ν i * E i :=
    bandit_regret_decomposition ν hν.1 π n
  set P : Fin k → Prop := fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i with hP
  -- split the sum at the deterministic threshold
  have hsplit :
      (∑ i, banditGap ν i * E i) =
        (∑ i ∈ Finset.univ.filter P, banditGap ν i * E i) +
          (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), banditGap ν i * E i) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- the small-gap arms contribute at most 8 sqrt(k n)
  have hsmall :
      (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), banditGap ν i * E i)
        ≤ 8 * Real.sqrt ((k : ℝ) * n) := by
    have hstep :
        (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), banditGap ν i * E i)
          ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i),
              (8 * Real.sqrt ((k : ℝ) / n)) * E i := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hgap : banditGap ν i ≤ 8 * Real.sqrt ((k : ℝ) / n) := by
        have := (Finset.mem_filter.mp hi).2
        simpa [hP] using not_lt.mp this
      exact mul_le_mul_of_nonneg_right hgap (hEnonneg i)
    have hfac :
        (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i),
            (8 * Real.sqrt ((k : ℝ) / n)) * E i)
          = (8 * Real.sqrt ((k : ℝ) / n)) *
              ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), E i := by
      rw [Finset.mul_sum]
    have hsub :
        (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), E i) ≤ ∑ i, E i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ ↦ hEnonneg i)
    have hcoef : (0 : ℝ) ≤ 8 * Real.sqrt ((k : ℝ) / n) := by positivity
    -- 8 * sqrt (k / n) * n = 8 * sqrt (k * n)
    have hkey : (8 * Real.sqrt ((k : ℝ) / n)) * (n : ℝ) = 8 * Real.sqrt ((k : ℝ) * n) := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnR
      have hsnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
      have hsq : Real.sqrt ((k : ℝ) / n) * (n : ℝ) = Real.sqrt ((k : ℝ) * n) := by
        calc Real.sqrt ((k : ℝ) / n) * (n : ℝ)
            = (Real.sqrt (k : ℝ) / Real.sqrt (n : ℝ)) *
                (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
              rw [Real.sqrt_div hk0, Real.mul_self_sqrt hn0]
          _ = Real.sqrt (k : ℝ) * Real.sqrt (n : ℝ) := by
              field_simp
          _ = Real.sqrt ((k : ℝ) * n) := (Real.sqrt_mul hk0 _).symm
      rw [mul_assoc, hsq]
    calc
      (∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), banditGap ν i * E i)
          ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i),
              (8 * Real.sqrt ((k : ℝ) / n)) * E i := hstep
      _ = (8 * Real.sqrt ((k : ℝ) / n)) *
              ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ P i), E i := hfac
      _ ≤ (8 * Real.sqrt ((k : ℝ) / n)) * ∑ i, E i :=
            mul_le_mul_of_nonneg_left hsub hcoef
      _ = (8 * Real.sqrt ((k : ℝ) / n)) * (n : ℝ) := by rw [hsum]
      _ = 8 * Real.sqrt ((k : ℝ) * n) := hkey
  have h24 : (8 : ℝ) * Real.sqrt ((k : ℝ) * n) ≤ 24 * Real.sqrt ((k : ℝ) * n) := by
    have : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) * n) := Real.sqrt_nonneg _
    nlinarith
  rw [hdec, hsplit]
  linarith [hsmall, h24]
