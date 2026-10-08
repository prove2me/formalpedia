-- Prove2me | solution 1 for Goldbach.near_siegel_explicit_gap
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T02:39:24.0551+00:00
-- url     : https://prove2.me/submissions/2c004f3c-d499-43b9-b1a6-3e986c06a95c

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

namespace GoldbachNearSiegelGap

private lemma exp_neg_quadratic (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1-x+x^2/2 := by
  have hp : 0 ≤ 1-x+x^2/2 := by nlinarith [sq_nonneg (x-1)]
  have hh := mul_le_mul_of_nonneg_left (Real.quadratic_le_exp_of_nonneg hx) hp
  have hprod : 1 ≤ (1-x+x^2/2)*Real.exp x := by
    nlinarith [sq_nonneg (x^2)]
  have hmul : Real.exp (-x)*Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x]

set_option backward.isDefEq.respectTransparency false in
private lemma exp_neg_twelve : Real.exp (-12) ≤ 35/1380767 := by
  have hh := Real.sum_le_exp_of_nonneg (x := 12) (by norm_num) 10
  norm_num [Finset.sum_range_succ,Nat.factorial] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (-12))
  rw [← Real.exp_add] at hmul
  norm_num at hmul
  nlinarith

private lemma log_tail_bound (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    Real.exp (-(164/75)*max (142/25) ((109/100)*Real.log (1/ell))) ≤ ell^2 := by
  have hlog : Real.log ell ≤ 0 := Real.log_nonpos hell.le hell1
  have hL := le_max_right (142/25:ℝ) ((109/100)*Real.log (1/ell))
  rw [Real.log_div (by norm_num) (ne_of_gt hell),Real.log_one,zero_sub] at hL
  have he : -(164/75)*max (142/25) ((109/100)*Real.log (1/ell)) ≤
      2*Real.log ell := by
    rw [Real.log_div (by norm_num) (ne_of_gt hell),Real.log_one,zero_sub]
    nlinarith
  have hh := Real.exp_le_exp.mpr he
  have hid : Real.exp (2*Real.log ell) = ell^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log hell]
    ring
  exact hid ▸ hh

private lemma small_gap (ell : ℝ) (hell : 0 < ell) (hsmall : ell ≤ 1/200) :
    Real.exp (-(33/5)*ell) +
      202*Real.exp (-(164/75)*max (142/25) ((109/100)*Real.log (1/ell))) ≤
      1-(54811/10000)*ell := by
  have h1 := exp_neg_quadratic ((33/5)*ell) (by nlinarith)
  have heq : -((33/5:ℝ)*ell) = -(33/5)*ell := by ring
  rw [heq] at h1
  have h2 := log_tail_bound ell hell (by linarith)
  have hh : ell^2 ≤ ell/200 := by nlinarith [mul_nonneg hell.le (sub_nonneg.mpr hsmall)]
  nlinarith

private lemma large_gap (ell : ℝ) (hlower : 1/200 ≤ ell) :
    Real.exp (-(33/5)*ell) +
      202*Real.exp (-(164/75)*max (142/25) ((109/100)*Real.log (1/ell))) ≤ 1-1/40 := by
  have h1 : Real.exp (-(33/5)*ell) ≤ Real.exp (-(33/1000)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (-(164/75)*max (142/25) ((109/100)*Real.log (1/ell))) ≤
      Real.exp (-12) := by
    apply Real.exp_le_exp.mpr
    have hh := le_max_left (142/25:ℝ) ((109/100)*Real.log (1/ell))
    nlinarith
  have hquad := exp_neg_quadratic (33/1000) (by norm_num)
  have htail := exp_neg_twelve
  nlinarith

end GoldbachNearSiegelGap

theorem solution (c ell : ℝ) (hc : 0 < c) (hcell : c ≤ ell) :
    0 < min ((54811/10000)*min c (1/200)) (1/40) ∧
    Real.exp (-(33/5)*ell) +
      202*Real.exp (-(164/75)*max (142/25) ((109/100)*Real.log (1/ell))) ≤
      1-min ((54811/10000)*min c (1/200)) (1/40) := by
  have hell0 : 0 < ell := hc.trans_le hcell
  have hgap : 0 < min ((54811/10000)*min c (1/200)) (1/40) := by
    apply lt_min
    · exact mul_pos (by norm_num) (lt_min hc (by norm_num))
    · norm_num
  refine ⟨hgap,?_⟩
  by_cases hs : ell ≤ 1/200
  · have hh := GoldbachNearSiegelGap.small_gap ell hell0 hs
    have hmin : min c (1/200) ≤ ell := (min_le_left _ _).trans hcell
    have hbound := min_le_left ((54811/10000)*min c (1/200)) (1/40)
    nlinarith
  · have hh := GoldbachNearSiegelGap.large_gap ell (le_of_not_ge hs)
    have hbound := min_le_right ((54811/10000)*min c (1/200)) (1/40)
    linarith

#print axioms solution
