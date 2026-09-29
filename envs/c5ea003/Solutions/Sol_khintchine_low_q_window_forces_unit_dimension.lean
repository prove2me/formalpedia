-- Prove2me | solution 1 for khintchine_low_q_window_forces_unit_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T21:00:38.11689+00:00
-- url     : https://prove2.me/submissions/d49683a2-161d-49f9-a1d7-c9795776a10f

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

theorem solution :
    ∀ (β : ℝ), 2 < β →
    ∀ (n₁ n₂ q : ℕ),
      1 ≤ q →
      ¬ 2 ≤ q →
      (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
      max n₁ n₂ ≤ 1 := by
  intro β hβ n₁ n₂ q hqOne hqNotTwo hqlog
  have hq_lt_two : q < 2 := Nat.lt_of_not_ge hqNotTwo
  have hq_le_one : q ≤ 1 := Nat.lt_succ_iff.mp hq_lt_two
  have hq_eq : q = 1 := le_antisymm hq_le_one hqOne
  by_contra hdim
  have hmax_ge_two : 2 ≤ max n₁ n₂ := by
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hdim)
  have hlog_mono : Real.log (2 : ℝ) ≤
      Real.log ((max n₁ n₂ : ℕ) : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hmax_ge_two)
  have hlog_two_half : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog_two_nonneg : 0 ≤ Real.log (2 : ℝ) := le_of_lt (by linarith)
  have hbeta_nonneg : 0 ≤ β :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
  have hmul_le :
      (2 : ℝ) * Real.log 2 ≤
        β * Real.log ((max n₁ n₂ : ℕ) : ℝ) := by
    exact mul_le_mul (le_of_lt hβ) hlog_mono hlog_two_nonneg hbeta_nonneg
  have hone_lt_two_log : (1 : ℝ) < 2 * Real.log 2 := by nlinarith
  have hone_lt :
      (1 : ℝ) < β * Real.log ((max n₁ n₂ : ℕ) : ℝ) :=
    lt_of_lt_of_le hone_lt_two_log hmul_le
  have hqcast : (q : ℝ) = 1 := by exact_mod_cast hq_eq
  rw [hqcast] at hqlog
  linarith
