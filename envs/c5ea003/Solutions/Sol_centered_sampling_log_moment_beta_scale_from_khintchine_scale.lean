-- Prove2me | solution 1 for centered_sampling_log_moment_beta_scale_from_khintchine_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T08:25:03.806979+00:00
-- url     : https://prove2.me/submissions/7b2b2784-29a1-4766-bbb2-91ee5420189a

import Definitions.Def_matrix_completion_rademacher
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    (Cq : ℝ) :
    0 < Cq →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Cq * Real.sqrt
            (((q : ℝ) * (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (Cmoment * Real.sqrt
            ((β * (↑(max n₁ n₂)) *
                Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q := by
  intro hCq
  refine ⟨2 * Cq, by positivity, ?_⟩
  intro β hβ n₁ n₂ m q X hn₁ hn₂ _hm hmLower hqOne _hqLower hqUpper hMoment
  let n : ℕ := max n₁ n₂
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let base : ℝ := (β * (n : ℝ) * Real.log (n : ℝ)) / p
  let qbase : ℝ := ((q : ℝ) * (n : ℝ)) / p
  have hn_pos_nat : 0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hq_pos_real : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqOne)
  have hbeta_pos : 0 < β := lt_trans (by norm_num : (0 : ℝ) < 2) hβ
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    have hupper_pos : 0 < 2 * (β * Real.log (n : ℝ)) := lt_of_lt_of_le hq_pos_real (by simpa [n] using hqUpper)
    nlinarith
  have hsample_pos :
      0 < β * (n : ℝ) * Real.log (n : ℝ) := by positivity
  have hm_pos : 0 < (m : ℝ) := lt_of_lt_of_le hsample_pos (by simpa [n, mul_assoc] using hmLower)
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hbase_nonneg : 0 ≤ base := by
    dsimp [base, p]
    positivity
  have hqbase_nonneg : 0 ≤ qbase := by
    dsimp [qbase, p]
    positivity
  have hqbase_le_two_base : qbase ≤ 2 * base := by
    have hq_mul :
        (q : ℝ) * (n : ℝ) ≤
          (2 * (β * Real.log (n : ℝ))) * (n : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by simpa [n] using hqUpper) hn_nonneg
    have hdiv :
        ((q : ℝ) * (n : ℝ)) / p ≤
          ((2 * (β * Real.log (n : ℝ))) * (n : ℝ)) / p := by
      exact div_le_div_of_nonneg_right hq_mul (le_of_lt hp_pos)
    dsimp [qbase, base]
    convert hdiv using 1 <;> ring
  have hsqrt_qbase_le :
      Real.sqrt qbase ≤ 2 * Real.sqrt base := by
    have hsqrt_mono : Real.sqrt qbase ≤ Real.sqrt (2 * base) :=
      Real.sqrt_le_sqrt hqbase_le_two_base
    have htwo_base_nonneg : 0 ≤ 2 * base := by positivity
    have hsqrt_two_base_le : Real.sqrt (2 * base) ≤ 2 * Real.sqrt base := by
      have hsq :
          (Real.sqrt (2 * base)) ^ 2 ≤ (2 * Real.sqrt base) ^ 2 := by
        calc
          (Real.sqrt (2 * base)) ^ 2 = 2 * base := Real.sq_sqrt htwo_base_nonneg
          _ ≤ 4 * base := by nlinarith [hbase_nonneg]
          _ = (2 * Real.sqrt base) ^ 2 := by
            calc
              4 * base = 4 * (Real.sqrt base) ^ 2 := by
                rw [Real.sq_sqrt hbase_nonneg]
              _ = (2 * Real.sqrt base) ^ 2 := by ring
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp hsq
    exact le_trans hsqrt_mono hsqrt_two_base_le
  have hentry_nonneg : 0 ≤ entrySupNorm X := by
    let i0 : Fin n₁ := ⟨0, hn₁⟩
    let j0 : Fin n₂ := ⟨0, hn₂⟩
    exact le_trans (abs_nonneg (X i0 j0))
      (le_trans
        (le_ciSup
          (Finite.bddAbove_range (fun j : Fin n₂ => |X i0 j|)) j0)
        (le_ciSup
          (Finite.bddAbove_range
            (fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)) i0))
  have hscale :
      Cq * Real.sqrt qbase * entrySupNorm X ≤
        (2 * Cq) * Real.sqrt base * entrySupNorm X := by
    have hCq_nonneg : 0 ≤ Cq := le_of_lt hCq
    nlinarith [mul_le_mul_of_nonneg_left hsqrt_qbase_le hCq_nonneg,
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt_qbase_le hCq_nonneg) hentry_nonneg]
  have hpow :
      (Cq * Real.sqrt qbase * entrySupNorm X) ^ q ≤
        ((2 * Cq) * Real.sqrt base * entrySupNorm X) ^ q := by
    exact pow_le_pow_left₀ (by positivity) hscale q
  have hMoment' :
      bernoulliExpectation p
          (fun Omega =>
            spectralNorm
              (centeredSamplingFluctuation Omega p X) ^ q) ≤
        (Cq * Real.sqrt qbase * entrySupNorm X) ^ q := by
    simpa [p, qbase, n] using hMoment
  exact le_trans hMoment' (by simpa [p, base, n, mul_assoc] using hpow)
