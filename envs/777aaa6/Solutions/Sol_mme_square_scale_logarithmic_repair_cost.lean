-- Prove2me | solution 1 for mme_square_scale_logarithmic_repair_cost
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:11:00.843681+00:00
-- url     : https://prove2.me/submissions/fec401ec-efa7-4047-9f49-d98f73b6dd96

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

open Real
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (C : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ cap : ℕ, cap ≤ 7 ^ (C * k ^ 2) →
      let h := Nat.log k cap + 1
      1 < k ∧ cap < k ^ h ∧ Real.log ((8 : ℝ) ^ h) < delta * (k : ℝ) ^ 2 := by
  have h7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  let B := 2 * (C : ℝ) * Real.log 7 * Real.log 8 / delta
  obtain ⟨K,hK⟩ := exists_nat_gt (max 2 (max (Real.exp B) (2 * Real.log 8 / delta)))
  refine ⟨K, fun k hk cap hcap ↦ ?_⟩
  have hkR : max 2 (max (Real.exp B) (2 * Real.log 8 / delta)) < (k : ℝ) :=
    hK.trans_le (by exact_mod_cast hk)
  have hk2 : (2 : ℝ) < k := (le_max_left _ _).trans_lt hkR
  have hkNat : 1 < k := by exact_mod_cast (show (1 : ℝ) < k by linarith)
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : 0 < Real.log k := Real.log_pos (by linarith)
  have hB : B < Real.log k := by
    have he : Real.exp B < (k : ℝ) := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hkR)
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) he
  have hsmall : 2 * Real.log 8 / delta < (k : ℝ) :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hkR)
  have htail : Real.log 8 < delta * (k : ℝ) ^ 2 / 2 := by
    have h := (div_lt_iff₀ hdelta).mp hsmall
    have hkpow : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  let h := Nat.log k cap + 1
  have hmono : (Nat.log k cap : ℝ) ≤ Nat.log k (7 ^ (C * k ^ 2)) := by
    exact_mod_cast Nat.log_mono_right (b := k) hcap
  have hNat : (Nat.log k cap : ℝ) ≤ Real.logb k (7 ^ (C * k ^ 2) : ℕ) :=
    hmono.trans (Real.natLog_le_logb _ _)
  have hh : (h : ℝ) ≤ (C : ℝ) * (k : ℝ) ^ 2 * Real.log 7 / Real.log k + 1 := by
    dsimp [h]
    simp only [Nat.cast_add, Nat.cast_one]
    have hb : Real.logb k (7 ^ (C * k ^ 2) : ℕ) =
        (C : ℝ) * (k : ℝ) ^ 2 * Real.log 7 / Real.log k := by
      simp only [Real.logb, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
    rw [hb] at hNat
    linarith
  have hmain : ((C : ℝ) * (k : ℝ) ^ 2 * Real.log 7 / Real.log k) * Real.log 8 <
      delta * (k : ℝ) ^ 2 / 2 := by
    have h := (div_lt_iff₀ hdelta).mp hB
    change 2 * (C : ℝ) * Real.log 7 * Real.log 8 < Real.log k * delta at h
    have ht := mul_lt_mul_of_pos_right h (sq_pos_of_pos hk0)
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hlog).mpr
    nlinarith
  refine ⟨hkNat, Nat.lt_pow_succ_log_self hkNat cap, ?_⟩
  rw [Real.log_pow]
  have hm := mul_le_mul_of_nonneg_right hh h8.le
  nlinarith
