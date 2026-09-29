-- Prove2me | solution 1 for BanditAlgorithm.adversarial_bandit_exp3_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-07-18T16:28:58.083975+00:00
-- url     : https://prove2.me/submissions/b7d90e04-269b-41a5-bc75-8840cb0a7839

import Theorems.Thm_BanditAlgorithm_exp3_expected_regret_generic_bound

open MeasureTheory ProbabilityTheory

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp3Policy (Real.sqrt (2 * Real.log k / (n * k))) π) :
    BanditAlgorithm.adversarialRegret n x π ≤ Real.sqrt (2 * n * k * Real.log k) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0R : (0 : ℝ) < k := lt_trans (by norm_num) hkR
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  have hN : (0 : ℝ) < n * k := mul_pos hnR hk0R
  have harg : 0 < (2 * Real.log k / (n * k) : ℝ) := div_pos (mul_pos (by norm_num) hlog) hN
  let η : ℝ := Real.sqrt (2 * Real.log k / (n * k))
  have hη : 0 < η := Real.sqrt_pos.2 harg
  have hηsq : η ^ 2 = 2 * Real.log k / (n * k) := by
    dsimp [η]
    exact Real.sq_sqrt (le_of_lt harg)
  have hηeq : η ^ 2 * (n * k) = 2 * Real.log k := by
    exact (eq_div_iff (ne_of_gt hN)).mp hηsq
  have hbase := BanditAlgorithm.exp3_expected_regret_generic_bound
    hk n hn x hx π η hη hπ
  have hbig : 0 ≤ (2 * n * k * Real.log k : ℝ) := by positivity
  have hsqrt_sq : (Real.sqrt (2 * n * k * Real.log k) : ℝ) ^ 2 =
      2 * n * k * Real.log k := Real.sq_sqrt hbig
  have hsqrt0 : 0 ≤ Real.sqrt (2 * n * k * Real.log k) := Real.sqrt_nonneg _
  have hopt : Real.log k / η + η * n * k / 2 =
      Real.sqrt (2 * n * k * Real.log k) := by
    have hηne : η ≠ 0 := ne_of_gt hη
    have hfirst : Real.log k / η = η * n * k / 2 := by
      field_simp
      nlinarith [hηeq]
    rw [hfirst]
    have hprod : η * n * k = Real.sqrt (2 * n * k * Real.log k) := by
      have hprod0 : 0 ≤ η * n * k := by positivity
      have hprod_sq : (η * n * k) ^ 2 = 2 * n * k * Real.log k := by
        calc
          (η * n * k) ^ 2 = (η ^ 2 * (n * k)) * (n * k) := by ring
          _ = (2 * Real.log k) * (n * k) := by rw [hηeq]
          _ = 2 * n * k * Real.log k := by ring
      nlinarith [hprod_sq, hsqrt_sq]
    nlinarith
  exact hbase.trans_eq hopt
