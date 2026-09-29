-- Prove2me | solution 1 for mme_eventually_linear_le_exp_linear_sub_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T19:38:30.876798+00:00
-- url     : https://prove2.me/submissions/0891dab0-582c-44c7-b28a-e135b2d80e8a

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Filter Topology

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      a * (((n + 1 : ℕ) : ℝ)) ≤
        Real.exp
          (b * (n : ℝ) - C * Real.sqrt (((n + 1 : ℕ) : ℝ))) := by
  let e : ℝ := b / (2 * (C + 1))
  let c0 : ℝ := (C + 1) ^ 2 / (2 * b)
  let c1 : ℝ := c0 + b / 2
  have hCp : 0 < C + 1 := by linarith
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hc1 : 0 ≤ c1 := by
    dsimp only [c1, c0]
    positivity
  have hbhalf : 0 < b / 2 := by positivity
  have htend :
      Tendsto
        (fun n : ℕ ↦
          Real.exp ((b / 2) * (n : ℝ)) / ((n : ℝ) ^ (1 : ℝ)))
        atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop 1 (b / 2) hbhalf).comp
      tendsto_natCast_atTop_atTop
  have hratio : ∀ᶠ n : ℕ in atTop,
      2 * a * Real.exp c1 ≤
        Real.exp ((b / 2) * (n : ℝ)) / ((n : ℝ) ^ (1 : ℝ)) :=
    (tendsto_atTop.1 htend (2 * a * Real.exp c1))
  filter_upwards [hratio, eventually_ge_atTop 1] with n hnratio hn1
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hy : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  let s : ℝ := Real.sqrt (((n + 1 : ℕ) : ℝ))
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have hs2 : s ^ 2 = (((n + 1 : ℕ) : ℝ)) := by
    dsimp only [s]
    exact Real.sq_sqrt hy
  have hamgm : s ≤ e * (((n + 1 : ℕ) : ℝ)) + 1 / (4 * e) := by
    have hsq := sq_nonneg (2 * e * s - 1)
    rw [← hs2]
    rw [add_comm, ← sub_le_iff_le_add,
      le_div_iff₀ (by positivity : (0 : ℝ) < 4 * e)]
    nlinarith
  have hroot :
      C * s ≤ (b / 2) * (((n + 1 : ℕ) : ℝ)) + c0 := by
    have hCle : C ≤ C + 1 := by linarith
    have hscale : C * s ≤ (C + 1) * s :=
      mul_le_mul_of_nonneg_right hCle hs
    have heq1 : (C + 1) * e = b / 2 := by
      dsimp only [e]
      field_simp
    have heq2 : (C + 1) * (1 / (4 * e)) = c0 := by
      dsimp only [e, c0]
      field_simp
      ring
    calc
      C * s ≤ (C + 1) * s := hscale
      _ ≤ (C + 1) *
          (e * (((n + 1 : ℕ) : ℝ)) + 1 / (4 * e)) := by gcongr
      _ = (b / 2) * (((n + 1 : ℕ) : ℝ)) + c0 := by
        rw [mul_add, ← mul_assoc, heq1, heq2]
  have hexpRatio :
      2 * a * Real.exp c1 * (n : ℝ) ≤
        Real.exp ((b / 2) * (n : ℝ)) := by
    have hnratio' : 2 * a * Real.exp c1 ≤
        Real.exp ((b / 2) * (n : ℝ)) / (n : ℝ) := by
      simpa only [Real.rpow_one] using hnratio
    exact (le_div_iff₀ hnR).1 hnratio'
  have hnSucc : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    push_cast
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn1]
  have hscaled :
      a * (((n + 1 : ℕ) : ℝ)) * Real.exp c1 ≤
        Real.exp ((b / 2) * (n : ℝ)) := by
    calc
      a * (((n + 1 : ℕ) : ℝ)) * Real.exp c1
          ≤ a * (2 * (n : ℝ)) * Real.exp c1 := by gcongr
      _ = 2 * a * Real.exp c1 * (n : ℝ) := by ring
      _ ≤ Real.exp ((b / 2) * (n : ℝ)) := hexpRatio
  have hbase :
      a * (((n + 1 : ℕ) : ℝ)) ≤
        Real.exp ((b / 2) * (n : ℝ) - c1) := by
    rw [Real.exp_sub]
    exact (le_div_iff₀ (Real.exp_pos c1)).2 hscaled
  have hexponent :
      (b / 2) * (n : ℝ) - c1 ≤
        b * (n : ℝ) - C * s := by
    dsimp only [c1]
    push_cast at hroot ⊢
    nlinarith
  exact hbase.trans (Real.exp_le_exp.mpr hexponent)
