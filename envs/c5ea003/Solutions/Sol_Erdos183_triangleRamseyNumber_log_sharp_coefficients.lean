-- Prove2me | solution 1 for Erdos183.triangleRamseyNumber_log_sharp_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:34:03.304095+00:00
-- url     : https://prove2.me/submissions/b0e69570-1bcd-4e80-9520-07b3a7229eef

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Theorems.Thm_Erdos183_quantitativeLowerBound_explicit_all
import Theorems.Thm_Erdos183_triangleRamseyNumber_factorial_upper

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        ((1 / 3 : ℝ) - ε) * (k : ℝ) * Real.log (k : ℝ) ≤
            Real.log (triangleRamseyNumber k : ℝ) ∧
          Real.log (triangleRamseyNumber k : ℝ) ≤
            (1 + ε) * (k : ℝ) * Real.log (k : ℝ) := by
  intro ε hε
  let c : ℝ := 1 / (6 * Real.exp 38)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        ‖Real.log (k : ℝ)‖ ≤ c * ‖(k : ℝ) ^ ε‖ := by
    simpa [Function.comp_def] using
      ((isLittleO_log_rpow_atTop hε).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).bound hc
  have hfour :
      ∀ᶠ k : ℕ in atTop,
        ‖Real.log (4 : ℝ)‖ ≤ ε * ‖Real.log (k : ℝ)‖ := by
    simpa [Function.comp_def] using
      ((Real.isLittleO_const_log_atTop (c := Real.log (4 : ℝ))).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))).bound hε
  filter_upwards [hsmall, hfour, eventually_ge_atTop 2] with k hk hfour' hk2
  have hx : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hrpow : 0 < (k : ℝ) ^ ε := Real.rpow_pos_of_pos hx _
  have hsmall' : Real.log (k : ℝ) ≤ c * (k : ℝ) ^ ε := by
    rw [Real.norm_eq_abs, abs_of_pos hlog,
      Real.norm_eq_abs, abs_of_pos hrpow] at hk
    exact hk
  have hfourlog : Real.log (4 : ℝ) ≤ ε * Real.log (k : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.log_pos (by norm_num)),
      Real.norm_eq_abs, abs_of_pos hlog] at hfour'
    exact hfour'
  have hroot : 0 < (k : ℝ) ^ ((1 / 3 : ℝ) - ε) :=
    Real.rpow_pos_of_pos hx _
  have hbase :
      (k : ℝ) ^ ((1 / 3 : ℝ) - ε) ≤
        c * (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) := by
    apply (le_div_iff₀ hlog).mpr
    calc
      (k : ℝ) ^ ((1 / 3 : ℝ) - ε) * Real.log (k : ℝ) ≤
          (k : ℝ) ^ ((1 / 3 : ℝ) - ε) *
            (c * (k : ℝ) ^ ε) := by gcongr
      _ = c * ((k : ℝ) ^ ((1 / 3 : ℝ) - ε) *
          (k : ℝ) ^ ε) := by ring
      _ = c * (k : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring_nf
  have hRamseyLower :
      ((k : ℝ) ^ ((1 / 3 : ℝ) - ε)) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
    calc
      ((k : ℝ) ^ ((1 / 3 : ℝ) - ε)) ^ k ≤
          (c * (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k := by
            gcongr
      _ ≤ (triangleRamseyNumber k : ℝ) := by
        simpa [c] using quantitativeLowerBound_explicit_all k hk2
  have hRamseyPositive : 0 < (triangleRamseyNumber k : ℝ) :=
    lt_of_lt_of_le (pow_pos hroot k) hRamseyLower
  have hRamseyUpper :
      (triangleRamseyNumber k : ℝ) ≤ 4 * (k : ℝ) ^ k := by
    have hnat : triangleRamseyNumber k ≤ 4 * k ^ k :=
      (triangleRamseyNumber_factorial_upper k).trans
        (Nat.mul_le_mul_left 4 (Nat.factorial_le_pow k))
    exact_mod_cast hnat
  constructor
  · calc
      ((1 / 3 : ℝ) - ε) * (k : ℝ) * Real.log (k : ℝ) =
          Real.log (((k : ℝ) ^ ((1 / 3 : ℝ) - ε)) ^ k) := by
            rw [Real.log_pow, Real.log_rpow hx]
            ring
      _ ≤ Real.log (triangleRamseyNumber k : ℝ) :=
        Real.log_le_log (pow_pos hroot k) hRamseyLower
  · calc
      Real.log (triangleRamseyNumber k : ℝ) ≤
          Real.log (4 * (k : ℝ) ^ k) :=
        Real.log_le_log hRamseyPositive hRamseyUpper
      _ = Real.log 4 + (k : ℝ) * Real.log (k : ℝ) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ hx.ne'), Real.log_pow]
      _ ≤ (1 + ε) * (k : ℝ) * Real.log (k : ℝ) := by
        have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        nlinarith [mul_nonneg (sub_nonneg.mpr hkreal)
          (mul_nonneg hε.le hlog.le)]
