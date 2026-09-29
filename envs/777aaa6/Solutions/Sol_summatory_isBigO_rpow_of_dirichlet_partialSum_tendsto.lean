-- Prove2me | solution 1 for summatory_isBigO_rpow_of_dirichlet_partialSum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T19:52:58.615701+00:00
-- url     : https://prove2.me/submissions/fdf49d97-6c31-4058-b292-9227d0d7a5e5

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

open Filter Finset

/-- Telescoping sum of consecutive real powers. -/
theorem telescope_rpow (σ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n + 1 : ℝ) ^ σ - (n : ℝ) ^ σ) = ((N : ℝ) + 1) ^ σ - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih]
      push_cast
      ring

/-- Abel summation identity: the partial sums of `a` in terms of the partial sums of the
Dirichlet-weighted sequence `n ↦ a n * n ^ (-σ)`. -/
theorem abel_identity (a : ℕ → ℂ) (σ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + 1), a n)
      = ((((N : ℝ) + 1) ^ σ : ℝ) : ℂ) * (∑ n ∈ Finset.Icc 1 (N + 1), a n * ((n : ℝ) ^ (-σ) : ℝ))
        - ∑ n ∈ Finset.Icc 1 N,
            ((((n + 1 : ℝ) ^ σ - (n : ℝ) ^ σ : ℝ) : ℂ) *
              (∑ m ∈ Finset.Icc 1 n, a m * ((m : ℝ) ^ (-σ) : ℝ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hpos : (0 : ℝ) < (N : ℝ) + 1 + 1 := by positivity
      have hinv : (((N : ℝ) + 1 + 1) ^ σ) * (((N : ℝ) + 1 + 1) ^ (-σ)) = 1 := by
        rw [← Real.rpow_add hpos]
        simp
      have hinvC : ((((N : ℝ) + 1 + 1) ^ σ : ℝ) : ℂ) * ((((N : ℝ) + 1 + 1) ^ (-σ) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, hinv, Complex.ofReal_one]
      have e1 : (∑ n ∈ Finset.Icc 1 (N + 1 + 1), a n)
          = (∑ n ∈ Finset.Icc 1 (N + 1), a n) + a (N + 1 + 1) :=
        Finset.sum_Icc_succ_top (by omega) (fun n => a n)
      have e2 : (∑ n ∈ Finset.Icc 1 (N + 1 + 1), a n * ((n : ℝ) ^ (-σ) : ℝ))
          = (∑ n ∈ Finset.Icc 1 (N + 1), a n * ((n : ℝ) ^ (-σ) : ℝ))
            + a (N + 1 + 1) * ((((N + 1 + 1 : ℕ) : ℝ)) ^ (-σ) : ℝ) :=
        Finset.sum_Icc_succ_top (by omega) (fun n => a n * ((n : ℝ) ^ (-σ) : ℝ))
      have e3 : (∑ n ∈ Finset.Icc 1 (N + 1),
            ((((n + 1 : ℝ) ^ σ - (n : ℝ) ^ σ : ℝ) : ℂ) *
              (∑ m ∈ Finset.Icc 1 n, a m * ((m : ℝ) ^ (-σ) : ℝ))))
          = (∑ n ∈ Finset.Icc 1 N,
              ((((n + 1 : ℝ) ^ σ - (n : ℝ) ^ σ : ℝ) : ℂ) *
                (∑ m ∈ Finset.Icc 1 n, a m * ((m : ℝ) ^ (-σ) : ℝ))))
            + ((((((N + 1 : ℕ) : ℝ) + 1) ^ σ - (((N + 1 : ℕ) : ℝ)) ^ σ : ℝ)) : ℂ) *
              (∑ m ∈ Finset.Icc 1 (N + 1), a m * ((m : ℝ) ^ (-σ) : ℝ)) :=
        Finset.sum_Icc_succ_top (by omega)
          (fun n => ((((n + 1 : ℝ) ^ σ - (n : ℝ) ^ σ : ℝ) : ℂ) *
              (∑ m ∈ Finset.Icc 1 n, a m * ((m : ℝ) ^ (-σ) : ℝ))))
      rw [e1, e2, e3, ih]
      push_cast
      push_cast at hinvC
      linear_combination (-(a (N + 1 + 1))) * hinvC

theorem solution (a : ℕ → ℂ) (σ : ℝ) (hσ : 0 < σ) (L : ℂ)
    (h : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * ((n : ℝ) ^ (-σ) : ℝ))
      Filter.atTop (nhds L)) :
    Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n)
      (fun N : ℕ => (N : ℝ) ^ σ) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ N : ℕ,
      ‖∑ n ∈ Finset.Icc 1 N, a n * ((n : ℝ) ^ (-σ) : ℝ)‖ ≤ M := by
    obtain ⟨M, hM⟩ := h.norm.bddAbove_range
    exact ⟨M, fun N => hM ⟨N, rfl⟩⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine Asymptotics.IsBigO.of_bound (2 * M) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  have hstep : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) ^ σ - (n : ℝ) ^ σ := by
    intro n
    have : (n : ℝ) ^ σ ≤ ((n : ℝ) + 1) ^ σ :=
      Real.rpow_le_rpow (by positivity) (by linarith) hσ.le
    linarith
  have hsum : ‖∑ n ∈ Finset.Icc 1 K,
        (((((n : ℝ) + 1) ^ σ - (n : ℝ) ^ σ : ℝ)) : ℂ) *
          (∑ m ∈ Finset.Icc 1 n, a m * ((m : ℝ) ^ (-σ) : ℝ))‖
      ≤ (((K : ℝ) + 1) ^ σ - 1) * M := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ n ∈ Finset.Icc 1 K,
        ‖(((((n : ℝ) + 1) ^ σ - (n : ℝ) ^ σ : ℝ)) : ℂ) *
          (∑ m ∈ Finset.Icc 1 n, a m * ((m : ℝ) ^ (-σ) : ℝ))‖
          ≤ (((n : ℝ) + 1) ^ σ - (n : ℝ) ^ σ) * M := by
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hstep n)]
      exact mul_le_mul_of_nonneg_left (hM n) (hstep n)
    refine le_trans (Finset.sum_le_sum this) ?_
    rw [← Finset.sum_mul, telescope_rpow σ K]
  have habs : ‖((((K : ℝ) + 1) ^ σ : ℝ) : ℂ) *
      (∑ n ∈ Finset.Icc 1 (K + 1), a n * ((n : ℝ) ^ (-σ) : ℝ))‖
      ≤ ((K : ℝ) + 1) ^ σ * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) σ)]
    exact mul_le_mul_of_nonneg_left (hM (K + 1)) (Real.rpow_nonneg (by positivity) σ)
  have hgoal : ‖∑ n ∈ Finset.Icc 1 (K + 1), a n‖ ≤ 2 * M * (((K : ℝ) + 1) ^ σ) := by
    rw [abel_identity a σ K]
    refine le_trans (norm_sub_le _ _) ?_
    have := add_le_add habs hsum
    nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ (K : ℝ) + 1 by positivity) σ]
  have habs' : |((K : ℝ) + 1) ^ σ| = ((K : ℝ) + 1) ^ σ :=
    abs_of_nonneg (Real.rpow_nonneg (by positivity) σ)
  simpa [habs'] using hgoal
