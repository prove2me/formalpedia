-- Prove2me | solution 1 for fixed_matrix_log_moment_scale_absorbs_markov_failure_factor
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T23:01:01.784384+00:00
-- url     : https://prove2.me/submissions/0fb86d88-b5d2-44bb-9459-7cf55c6c90fd

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem solution
    (Cmoment : ℝ) :
    0 < Cmoment →
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) *
          Real.log (↑(max n₁ n₂)) →
        (Cmoment * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q ≤
          (Ctail * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm X) ^ q *
            Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCm
  refine ⟨Cmoment * Real.exp 1, by positivity, ?_⟩
  intro β hβ n₁ n₂ m q X hn1 hn2 hm hq hqlog hmlog
  rw [show Real.rpow (↑(max n₁ n₂)) (-β) = (↑(max n₁ n₂) : ℝ) ^ (-β) from rfl]
  have hmaxpos : (0:ℝ) < (↑(max n₁ n₂)) := by
    have h : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
    exact_mod_cast h
  have hesn : (0:ℝ) ≤ entrySupNorm X := by
    unfold entrySupNorm
    exact Real.iSup_nonneg (fun _ => Real.iSup_nonneg (fun _ => abs_nonneg _))
  have hSesn : (0:ℝ) ≤ Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
      ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) * entrySupNorm X := mul_nonneg (Real.sqrt_nonneg _) hesn
  have hkey : (↑(max n₁ n₂) : ℝ) ^ β ≤ (Real.exp 1) ^ q := by
    rw [Real.rpow_def_of_pos hmaxpos, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [mul_one, mul_comm]
    linarith [hqlog]
  have hnβpos : (0:ℝ) < (↑(max n₁ n₂) : ℝ) ^ β := Real.rpow_pos_of_pos hmaxpos β
  have hexp_inv : (1:ℝ) ≤ (Real.exp 1) ^ q * (↑(max n₁ n₂) : ℝ) ^ (-β) := by
    rw [Real.rpow_neg (le_of_lt hmaxpos), ← div_eq_mul_inv, one_le_div hnβpos]
    exact hkey
  rw [show Cmoment * Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
        ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) * entrySupNorm X
      = Cmoment * (Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
        ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) * entrySupNorm X) from by ring,
     show Cmoment * Real.exp 1 * Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
        ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) * entrySupNorm X
      = (Cmoment * Real.exp 1) * (Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
        ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) * entrySupNorm X) from by ring,
     mul_pow, mul_pow, mul_pow]
  have hQ : (0:ℝ) ≤ (Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
      ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) * entrySupNorm X) ^ q := pow_nonneg hSesn q
  have hCmq : (0:ℝ) ≤ Cmoment ^ q := by positivity
  have hmain := mul_le_mul_of_nonneg_left hexp_inv (mul_nonneg hCmq hQ)
  ring_nf at hmain ⊢
  nlinarith [hmain]
