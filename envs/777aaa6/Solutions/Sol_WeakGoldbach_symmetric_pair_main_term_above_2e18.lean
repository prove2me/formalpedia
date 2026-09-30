-- Prove2me | solution 1 for WeakGoldbach.symmetric_pair_main_term_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T03:54:03.177644+00:00
-- url     : https://prove2.me/submissions/35041d6a-2f8b-42c4-9c46-905480c26a61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_weighted_symmetric_main_term_above_2e18
import Theorems.Thm_WeakGoldbach_prime_power_part_le_above_2e18
import Theorems.Thm_WeakGoldbach_singular_series_factor_ge_one

open Finset ArithmeticFunction

theorem solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      * (m : ℝ) / (Real.log m) ^ 2
      ≤ ((Finset.range (m - 1)).filter
        (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card := by
  set S : ℝ := ∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)
    with hSdef
  have hS : 1 ≤ S := hSdef ▸ WeakGoldbach.singular_series_factor_ge_one (2 * m)
  have hw := WeakGoldbach.weighted_symmetric_main_term_above_2e18 m hm
  have hpp := WeakGoldbach.prime_power_part_le_above_2e18 m hm
  rw [← hSdef] at hw hpp
  set s := Finset.range (m - 1) with hsdef
  set f : ℕ → ℝ := fun t =>
    (vonMangoldt (m - t) : ℝ) * (vonMangoldt (m + t) : ℝ) with hfdef
  have hterm : ∀ t ∈ s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)),
      f t ≤ (Real.log (2 * m)) ^ 2 := by
    intro t ht
    have htm : t ≤ m - 2 := by
      have hmem := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
      omega
    have h1 : (vonMangoldt (m - t) : ℝ) ≤ Real.log (2 * m) :=
      le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < m - t))
          (by exact_mod_cast (by omega : m - t ≤ 2 * m)))
    have h2 : (vonMangoldt (m + t) : ℝ) ≤ Real.log (2 * m) :=
      le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < m + t))
          (by exact_mod_cast (by omega : m + t ≤ 2 * m)))
    have h3 : (0 : ℝ) ≤ vonMangoldt (m + t) := ArithmeticFunction.vonMangoldt_nonneg
    have h4 : (0 : ℝ) ≤ Real.log (2 * m) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * m))
    calc f t = (vonMangoldt (m - t) : ℝ) * (vonMangoldt (m + t) : ℝ) := rfl
      _ ≤ Real.log (2 * m) * Real.log (2 * m) := mul_le_mul h1 h2 h3 h4
      _ = _ := by ring
  have hcard : (∑ t ∈ s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)), f t)
      ≤ (s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card
        * (Real.log (2 * m)) ^ 2 := by
    calc ∑ t ∈ s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)), f t
        ≤ ∑ _ ∈ s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)),
            (Real.log (2 * m)) ^ 2 := Finset.sum_le_sum hterm
      _ = (s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card
            * (Real.log (2 * m)) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : (∑ t ∈ s, f t)
      = (∑ t ∈ s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)), f t)
        + (∑ t ∈ s.filter (fun t => ¬ (Nat.Prime (m - t) ∧ Nat.Prime (m + t))), f t) := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)) f]
  have hmain : (s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card
        * (Real.log (2 * m)) ^ 2 ≥ S * m * (23 / 20) := by
    have h1 : (∑ t ∈ s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)), f t)
        ≥ S * m * (5 / 4) - S * m * (1 / 10) := by linarith
    calc (s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card
          * (Real.log (2 * m)) ^ 2
        ≥ S * m * (5 / 4) - S * m * (1 / 10) := le_trans h1 hcard
      _ = S * m * (23 / 20) := by ring
  have hlogpos : (0 : ℝ) < Real.log m :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlog2pos : (0 : ℝ) < Real.log (2 * m) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * m))
  have hlog2m : Real.log (2 * m) ≤ (21 / 20) * Real.log m := by
    have h20 : (20 : ℝ) * Real.log 2 ≤ Real.log m := by
      have hle : Real.log ((2 : ℝ) ^ 20) ≤ Real.log m := by
        apply Real.log_le_log (by positivity)
        have : ((2 : ℕ) ^ 20 : ℝ) ≤ (m : ℝ) :=
          by exact_mod_cast (by omega : 2 ^ 20 ≤ m)
        simpa using this
      rwa [Real.log_pow] at hle
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hm0]
    linarith
  have hcard2 : (s.filter (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card
      ≥ S * m * (23 / 20) / (Real.log (2 * m)) ^ 2 := by
    rw [ge_iff_le, div_le_iff₀ (sq_pos_of_pos hlog2pos)]
    linarith [hmain]
  apply le_trans _ hcard2
  have hmsq : (0 : ℝ) < (Real.log m) ^ 2 := sq_pos_of_pos hlogpos
  have h2msq : (0 : ℝ) < (Real.log (2 * m)) ^ 2 := sq_pos_of_pos hlog2pos
  have hSm : (0 : ℝ) < S * m := mul_pos (by linarith) (by exact_mod_cast (by omega : 0 < m))
  rw [div_le_iff₀ hmsq, div_mul_eq_mul_div, le_div_iff₀ h2msq]
  have hsq : (Real.log (2 * m)) ^ 2 ≤ (441 / 400) * (Real.log m) ^ 2 := by
    have hs : Real.log (2 * m) ≤ (21 / 20) * Real.log m := hlog2m
    have hnn1 : (0 : ℝ) ≤ Real.log (2 * m) := le_of_lt hlog2pos
    have hnn2 : (0 : ℝ) ≤ (21 / 20) * Real.log m :=
      mul_nonneg (by norm_num) (le_of_lt hlogpos)
    calc (Real.log (2 * m)) ^ 2 = Real.log (2 * m) * Real.log (2 * m) := sq _
      _ ≤ ((21 / 20) * Real.log m) * ((21 / 20) * Real.log m) :=
          mul_le_mul hs hs hnn1 hnn2
      _ = (441 / 400) * (Real.log m) ^ 2 := by ring
  calc S * m * (Real.log (2 * m)) ^ 2
      ≤ S * m * ((441 / 400) * (Real.log m) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (le_of_lt hSm)
    _ ≤ S * m * ((23 / 20) * (Real.log m) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hSm)
        have hmsqn : (0 : ℝ) ≤ (Real.log m) ^ 2 := sq_nonneg _
        nlinarith
    _ = S * m * (23 / 20) * (Real.log m) ^ 2 := by ring
