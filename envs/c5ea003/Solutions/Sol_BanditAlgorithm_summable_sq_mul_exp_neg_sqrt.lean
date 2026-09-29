-- Prove2me | solution 1 for BanditAlgorithm.summable_sq_mul_exp_neg_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T15:45:55.257384+00:00
-- url     : https://prove2.me/submissions/dabe6b3a-24b5-445a-9e48-5a54d7640176

import Definitions.Def_TrackAndStop
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# `∑ (m+1)² e^{−c√m} < ∞`

A sub-exponential decay absorbs any polynomial weight; here the weight is
quadratic, which is what a *delayed* covering argument costs — trading a delay
`θn` for a moment turns a linear weight into a quadratic one.

The comparison is `log x ≤ 4x^{1/4}`, obtained by applying `log ≤ 2√·` at `√x`
rather than at `x`, so that `4 log x ≤ 16 x^{1/4} ≤ c√x` once `x ≥ (16/c)^4` and
`e^{−c√x} ≤ x^{−4}`.  A fourth power leaves a convergent `∑ 1/(m+1)²` against the
quadratic weight.

Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), the tail estimate behind
Theorem 33.6; Garivier & Kaufmann, COLT 2016, Proposition 13.
-/

open Filter Topology

namespace BanditAlgorithm

theorem log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hlog : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos hs
  have hsplit : Real.log t = 2 * Real.log (Real.sqrt t) := by
    conv_lhs => rw [← hsq]
    rw [Real.log_mul hs.ne' hs.ne']
    ring
  rw [hsplit]
  linarith

theorem log_le_four_sqrt_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hhalf : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  have hstep : Real.log (Real.sqrt x) ≤ 2 * Real.sqrt (Real.sqrt x) :=
    log_le_two_sqrt hsx
  rw [hhalf]
  linarith

theorem summable_inv_succ_sq : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2 := by
  have h : Summable fun n : ℕ ↦ 1 / ((n : ℝ)) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine ((summable_nat_add_iff 1).mpr h).congr fun n ↦ ?_
  push_cast
  ring

theorem exp_neg_sqrt_le_inv_pow_four {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 ≤ x)
    (hthr : (16 / c) ^ 4 ≤ x) :
    Real.exp (-(c * Real.sqrt x)) ≤ 1 / x ^ 4 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hqx : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hsx
  -- `16/c ≤ x^{1/4}`, by taking square roots twice
  have hquart : 16 / c ≤ Real.sqrt (Real.sqrt x) := by
    have hpos : (0 : ℝ) ≤ 16 / c := by positivity
    have h2 : ((16 / c) ^ 2 : ℝ) ≤ Real.sqrt x := by
      have h := Real.sqrt_le_sqrt hthr
      rwa [show ((16 / c) ^ 4 : ℝ) = ((16 / c) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)] at h
    have h := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq hpos] at h
  have h16 : 16 ≤ c * Real.sqrt (Real.sqrt x) := by
    rw [div_le_iff₀ hc] at hquart
    linarith
  have hsq : Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) = Real.sqrt x :=
    Real.mul_self_sqrt hsx.le
  -- `4 log x ≤ 16 x^{1/4} ≤ c √x`
  have hlog : 4 * Real.log x ≤ c * Real.sqrt x := by
    have h1 : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := log_le_four_sqrt_sqrt hx0
    nlinarith [hqx, hc, h16, h1, hsq]
  have hexp4 : Real.exp (4 * Real.log x) = x ^ 4 := by
    have hrw : (4 : ℝ) * Real.log x = Real.log (x ^ 4) := by
      rw [Real.log_pow]; push_cast; ring
    rw [hrw, Real.exp_log (by positivity)]
  have hquad : (1 : ℝ) / x ^ 4 = Real.exp (-(4 * Real.log x)) := by
    rw [Real.exp_neg, hexp4, one_div]
  rw [hquad]
  exact Real.exp_le_exp.mpr (by linarith)


end BanditAlgorithm

open BanditAlgorithm

theorem solution {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℕ ↦ ((m : ℝ) + 1) ^ 2 * Real.exp (-(c * Real.sqrt (m : ℝ))) := by
  set M : ℕ := ⌈max 1 ((16 / c) ^ 4)⌉₊ + 1 with hMdef
  have hM1 : 1 ≤ M := by omega
  rw [← summable_nat_add_iff M]
  refine Summable.of_nonneg_of_le (fun m ↦ by positivity) (fun m ↦ ?_)
    (summable_inv_succ_sq.mul_left 4)
  set x : ℝ := ((m + M : ℕ) : ℝ) with hxdef
  have hxM : ((M : ℕ) : ℝ) ≤ x := by
    rw [hxdef]; exact_mod_cast Nat.le_add_left M m
  have hM1R : (1 : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hM1
  have hx1 : (1 : ℝ) ≤ x := le_trans hM1R hxM
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hthr : (16 / c) ^ 4 ≤ x := by
    refine le_trans ?_ hxM
    refine le_trans (le_max_right 1 _) ?_
    refine le_trans (Nat.le_ceil _) ?_
    have : (⌈max 1 ((16 / c) ^ 4)⌉₊ : ℝ) ≤ ((M : ℕ) : ℝ) := by
      rw [hMdef]; exact_mod_cast Nat.le_succ _
    exact this
  have hstep1 : Real.exp (-(c * Real.sqrt x)) ≤ 1 / x ^ 4 :=
    exp_neg_sqrt_le_inv_pow_four hc hx1 hthr
  have hstep2 : (x + 1) ^ 2 * Real.exp (-(c * Real.sqrt x)) ≤ 4 / x ^ 2 := by
    have hle : (x + 1) ^ 2 * Real.exp (-(c * Real.sqrt x)) ≤ (x + 1) ^ 2 * (1 / x ^ 4) := by
      have : (0 : ℝ) ≤ (x + 1) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hstep1 this
    refine le_trans hle ?_
    rw [mul_one_div, div_le_div_iff₀ (by positivity : (0:ℝ) < x ^ 4)
      (by positivity : (0:ℝ) < x ^ 2)]
    nlinarith [hx1, sq_nonneg x, sq_nonneg (x - 1)]
  have hstep3 : (4 : ℝ) / x ^ 2 ≤ 4 * (1 / ((m : ℝ) + 1) ^ 2) := by
    have hxm : ((m : ℝ) + 1) ≤ x := by
      rw [hxdef]
      have : (m : ℕ) + 1 ≤ m + M := by omega
      exact_mod_cast this
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hm1, hxm]
  calc ((((m + M : ℕ) : ℝ)) + 1) ^ 2 * Real.exp (-(c * Real.sqrt ((m + M : ℕ) : ℝ)))
      = (x + 1) ^ 2 * Real.exp (-(c * Real.sqrt x)) := by rw [hxdef]
    _ ≤ 4 / x ^ 2 := hstep2
    _ ≤ 4 * (1 / ((m : ℝ) + 1) ^ 2) := hstep3

