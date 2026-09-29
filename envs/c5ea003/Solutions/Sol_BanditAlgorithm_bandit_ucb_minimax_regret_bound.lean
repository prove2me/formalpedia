-- Prove2me | solution 1 for BanditAlgorithm.bandit_ucb_minimax_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-07-19T02:15:47.324707+00:00
-- url     : https://prove2.me/submissions/9b5640b7-55b3-422e-a5e0-ec4311a378de

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_bandit_canonical_occupation_identities
import Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_expected_pull_count
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), Theorem 7.2,
printed p. 108 (PDF p. 117). The proof splits arms at
`Δ = sqrt (16 * k * log n / n)`. Small-gap regret is bounded by `n * Δ`
using the total occupation identity; large-gap regret uses the per-arm UCB
pull-count bound from Theorem 7.1. The two terms are equal at this choice of
`Δ` and sum to `8 * sqrt (n * k * log n)`.
-/

open MeasureTheory ProbabilityTheory

theorem solution {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsUCBPolicy (1 / (n : ℝ) ^ 2) π) :
    BanditAlgorithm.banditRegret ν π n ≤
      8 * Real.sqrt (n * k * Real.log n) +
        3 * ∑ i, BanditAlgorithm.banditGap ν i := by
  classical
  have hgap_nonneg (i : Fin k) : 0 ≤ BanditAlgorithm.banditGap ν i := by
    rw [BanditAlgorithm.banditGap, sub_nonneg]
    exact Finite.le_ciSup (fun j : Fin k ↦ BanditAlgorithm.banditArmMean ν j) i
  let pulls : Fin k → ℝ := fun i ↦
    ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
      ∂(BanditAlgorithm.banditMeasure ν π n)
  have hpulls_nonneg (i : Fin k) : 0 ≤ pulls i := by
    dsimp [pulls]
    exact MeasureTheory.integral_nonneg fun _ ↦ by positivity
  have hdecomp :=
    BanditAlgorithm.bandit_regret_decomposition ν hν.1 π n
  change BanditAlgorithm.banditRegret ν π n ≤ _
  rw [hdecomp]
  change (∑ i, BanditAlgorithm.banditGap ν i * pulls i) ≤ _
  by_cases hn_one : n = 1
  · subst n
    have hterm (i : Fin k) :
        BanditAlgorithm.banditGap ν i * pulls i ≤
          3 * BanditAlgorithm.banditGap ν i := by
      by_cases hi0 : BanditAlgorithm.banditGap ν i = 0
      · simp [hi0]
      · have hi : 0 < BanditAlgorithm.banditGap ν i :=
          lt_of_le_of_ne (hgap_nonneg i) (Ne.symm hi0)
        have hb :=
          BanditAlgorithm.ucb_suboptimal_arm_expected_pull_count
            hk hν (by norm_num) hπ i hi
        change pulls i ≤ _ at hb
        have hm := mul_le_mul_of_nonneg_left hb (hgap_nonneg i)
        simpa [Real.log_one, hi0, mul_add, mul_comm] using hm
    calc
      (∑ i, BanditAlgorithm.banditGap ν i * pulls i) ≤
          ∑ i, 3 * BanditAlgorithm.banditGap ν i :=
        Finset.sum_le_sum fun i _ ↦ hterm i
      _ = 3 * ∑ i, BanditAlgorithm.banditGap ν i := by rw [Finset.mul_sum]
      _ = 8 * Real.sqrt ((1 : ℕ) * k * Real.log (1 : ℕ)) +
          3 * ∑ i, BanditAlgorithm.banditGap ν i := by norm_num
  · have hn_gt : 1 < n := by omega
    have hnR : (0 : ℝ) < n := by positivity
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn_gt)
    let s : ℝ := Real.sqrt ((n : ℝ) * (k : ℝ) * Real.log n)
    let Δ : ℝ := 4 * s / n
    have hs_pos : 0 < s := by
      dsimp [s]
      positivity
    have hΔ_pos : 0 < Δ := by
      dsimp [Δ]
      positivity
    have hs_sq : s ^ 2 = (n : ℝ) * (k : ℝ) * Real.log n := by
      dsimp [s]
      rw [Real.sq_sqrt]
      positivity
    have htotal : ∑ i, pulls i = (n : ℝ) := by
      simpa [pulls] using
        (BanditAlgorithm.bandit_canonical_occupation_identities ν hν.1 π n).2
    have hsmall_pulls :
        (∑ i ∈ Finset.univ.filter
            (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i < Δ), pulls i) ≤
          (n : ℝ) := by
      calc
        (∑ i ∈ Finset.univ.filter
            (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i < Δ), pulls i) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin k)), pulls i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun i _ _ ↦ hpulls_nonneg i)
        _ = (n : ℝ) := by simpa using htotal
    have hsmall :
        (∑ i ∈ Finset.univ.filter
            (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i < Δ),
            BanditAlgorithm.banditGap ν i * pulls i) ≤ 4 * s := by
      calc
        (∑ i ∈ Finset.univ.filter
            (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i < Δ),
            BanditAlgorithm.banditGap ν i * pulls i) ≤
            ∑ i ∈ Finset.univ.filter
              (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i < Δ),
              Δ * pulls i := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hi).2.le
            (hpulls_nonneg i)
        _ = Δ * ∑ i ∈ Finset.univ.filter
              (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i < Δ), pulls i := by
          rw [Finset.mul_sum]
        _ ≤ Δ * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hsmall_pulls hΔ_pos.le
        _ = 4 * s := by
          dsimp [Δ]
          field_simp
    have hrecip_eq : 16 * Real.log n / Δ = 4 * s / k := by
      dsimp [Δ]
      field_simp
      nlinarith [hs_sq]
    have hlarge_term (i : Fin k)
        (hi : i ∈ Finset.univ.filter
          (fun i : Fin k ↦ ¬ BanditAlgorithm.banditGap ν i < Δ)) :
        BanditAlgorithm.banditGap ν i * pulls i ≤
          3 * BanditAlgorithm.banditGap ν i + 4 * s / k := by
      have hΔgap : Δ ≤ BanditAlgorithm.banditGap ν i :=
        le_of_not_gt (Finset.mem_filter.mp hi).2
      have hgap_pos : 0 < BanditAlgorithm.banditGap ν i :=
        hΔ_pos.trans_le hΔgap
      have hb := BanditAlgorithm.ucb_suboptimal_arm_expected_pull_count
        hk hν hn hπ i hgap_pos
      change pulls i ≤ _ at hb
      have hm := mul_le_mul_of_nonneg_left hb (hgap_nonneg i)
      have hmul :
          BanditAlgorithm.banditGap ν i *
              (3 + 16 * Real.log n / BanditAlgorithm.banditGap ν i ^ 2) =
            3 * BanditAlgorithm.banditGap ν i +
              16 * Real.log n / BanditAlgorithm.banditGap ν i := by
        field_simp [ne_of_gt hgap_pos]
      rw [hmul] at hm
      calc
        BanditAlgorithm.banditGap ν i * pulls i ≤
            3 * BanditAlgorithm.banditGap ν i +
              16 * Real.log n / BanditAlgorithm.banditGap ν i := hm
        _ ≤ 3 * BanditAlgorithm.banditGap ν i + 16 * Real.log n / Δ := by
          gcongr
        _ = 3 * BanditAlgorithm.banditGap ν i + 4 * s / k := by
          rw [hrecip_eq]
    let large : Finset (Fin k) := Finset.univ.filter
      (fun i : Fin k ↦ ¬ BanditAlgorithm.banditGap ν i < Δ)
    have hlarge_gap_sum :
        (∑ i ∈ large, BanditAlgorithm.banditGap ν i) ≤
          ∑ i, BanditAlgorithm.banditGap ν i := by
      calc
        (∑ i ∈ large, BanditAlgorithm.banditGap ν i) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin k)), BanditAlgorithm.banditGap ν i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by intro i hi; simp) (fun i _ _ ↦ hgap_nonneg i)
        _ = ∑ i, BanditAlgorithm.banditGap ν i := rfl
    have hlarge_card : (large.card : ℝ) ≤ (k : ℝ) := by
      have hc : large.card ≤ k := by simpa using large.card_le_univ
      exact_mod_cast hc
    have hlarge :
        (∑ i ∈ large, BanditAlgorithm.banditGap ν i * pulls i) ≤
          3 * ∑ i, BanditAlgorithm.banditGap ν i + 4 * s := by
      calc
        (∑ i ∈ large, BanditAlgorithm.banditGap ν i * pulls i) ≤
            ∑ i ∈ large,
              (3 * BanditAlgorithm.banditGap ν i + 4 * s / k) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hlarge_term i (by simpa [large] using hi)
        _ = 3 * (∑ i ∈ large, BanditAlgorithm.banditGap ν i) +
              (large.card : ℝ) * (4 * s / k) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const]
          simp
        _ ≤ 3 * (∑ i, BanditAlgorithm.banditGap ν i) +
              (k : ℝ) * (4 * s / k) := by
          gcongr
        _ = 3 * (∑ i, BanditAlgorithm.banditGap ν i) + 4 * s := by
          field_simp
    have hpartition := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin k))
      (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i < Δ)
      (fun i ↦ BanditAlgorithm.banditGap ν i * pulls i)
    calc
      (∑ i, BanditAlgorithm.banditGap ν i * pulls i) =
          (∑ i ∈ Finset.univ.filter
            (fun i : Fin k ↦ BanditAlgorithm.banditGap ν i < Δ),
            BanditAlgorithm.banditGap ν i * pulls i) +
          (∑ i ∈ large, BanditAlgorithm.banditGap ν i * pulls i) := by
        simpa [large] using hpartition.symm
      _ ≤ 4 * s +
          (3 * ∑ i, BanditAlgorithm.banditGap ν i + 4 * s) :=
        add_le_add hsmall hlarge
      _ = 8 * Real.sqrt ((n : ℕ) * k * Real.log n) +
          3 * ∑ i, BanditAlgorithm.banditGap ν i := by
        change _ = 8 * s + _
        ring
