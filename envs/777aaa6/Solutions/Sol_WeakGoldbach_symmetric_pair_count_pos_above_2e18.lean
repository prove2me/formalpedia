-- Prove2me | solution 1 for WeakGoldbach.symmetric_pair_count_pos_above_2e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T22:48:56.878407+00:00
-- url     : https://prove2.me/submissions/e3bbed79-de09-4917-93f0-3691c5c03842
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_symmetric_pair_main_term_above_2e18
import Theorems.Thm_WeakGoldbach_singular_series_factor_ge_one

theorem solution (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    0 < ((Finset.range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card := by
  have hb := WeakGoldbach.symmetric_pair_main_term_above_2e18 m hm
  have hS := WeakGoldbach.singular_series_factor_ge_one (2 * m)
  have hlog : (0 : ℝ) < Real.log m := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < m)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hterm : (0 : ℝ) <
      (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
        * (m : ℝ) / (Real.log m) ^ 2 := by
    apply div_pos (mul_pos _ hmpos) (sq_pos_of_ne_zero hlog.ne')
    linarith
  have hcast : (0 : ℝ) <
      (((Finset.range (m - 1)).filter
        (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card : ℝ) :=
    lt_of_lt_of_le hterm hb
  exact_mod_cast hcast
