-- Prove2me | solution 1 for Martingale.norm_prod_sub_prod_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:04:54.186559+00:00
-- url     : https://prove2.me/submissions/3d87fd26-4a3e-4087-b269-0e47ddb174c9

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Finset

theorem solution (a b : ℕ → ℂ) (ha : ∀ k, ‖a k‖ ≤ 1) (hb : ∀ k, ‖b k‖ ≤ 1) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, a k - ∏ k ∈ Finset.range n, b k‖
      ≤ ∑ k ∈ Finset.range n, ‖a k - b k‖ := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hpa : ‖∏ k ∈ Finset.range m, a k‖ ≤ 1 := by
      refine le_trans (norm_prod_le _ _) ?_
      calc ∏ k ∈ Finset.range m, ‖a k‖ ≤ ∏ _k ∈ Finset.range m, (1:ℝ) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun k _ => ha k)
        _ = 1 := by simp
    have hsplit : (∏ k ∈ Finset.range (m + 1), a k) - ∏ k ∈ Finset.range (m + 1), b k
        = (∏ k ∈ Finset.range m, a k) * (a m - b m)
          + ((∏ k ∈ Finset.range m, a k) - ∏ k ∈ Finset.range m, b k) * b m := by
      simp only [Finset.prod_range_succ]; ring
    rw [hsplit, Finset.sum_range_succ]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖∏ k ∈ Finset.range m, a k‖ * ‖a m - b m‖ ≤ ‖a m - b m‖ := by
      nlinarith [norm_nonneg (a m - b m), norm_nonneg (∏ k ∈ Finset.range m, a k)]
    have h2 : ‖(∏ k ∈ Finset.range m, a k) - ∏ k ∈ Finset.range m, b k‖ * ‖b m‖
        ≤ ∑ k ∈ Finset.range m, ‖a k - b k‖ := by
      nlinarith [norm_nonneg ((∏ k ∈ Finset.range m, a k) - ∏ k ∈ Finset.range m, b k),
        norm_nonneg (b m), hb m, ih]
    linarith
