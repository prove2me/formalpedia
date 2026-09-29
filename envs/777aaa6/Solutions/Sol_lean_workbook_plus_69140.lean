-- Prove2me | solution 1 for lean_workbook_plus_69140
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:21:53.992624+00:00
-- url     : https://prove2.me/submissions/e5e6d609-6706-4419-9eb4-cda65f48fdaf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : 0 < a + b + c) (h : (a * b) / (c + 1) + (b * c) / (a + 1) + (c * a) / (b + 1) + 2 * (a + b + c) = 6) : a * b + b * c + c * a ≤ 2   := by
  let s := a + b + c
  let p := a * b + b * c + c * a
  let q := a * b * c
  have hs : 0 < s := by
    dsimp [s]
    by_contra hbad
    have haz : a = 0 := by linarith
    have hbz : b = 0 := by linarith
    have hcz : c = 0 := by linarith
    simp [haz, hbz, hcz] at h
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hd1 : c + 1 ≠ 0 := ne_of_gt (by positivity)
  have hd2 : a + 1 ≠ 0 := ne_of_gt (by positivity)
  have hd3 : b + 1 ≠ 0 := ne_of_gt (by positivity)
  have he : p ^ 2 + (3 * s - 5) * p + 2 * s ^ 2 - 4 * s - 6 = 9 * q := by
    dsimp [s, p, q]
    field_simp [hd1, hd2, hd3] at h
    nlinarith only [h]
  have hsp : 9 * q ≤ s * p := by
    dsimp [s, p, q]
    nlinarith [mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (c - a)), mul_nonneg hc (sq_nonneg (a - b))]
  have hs2 : 3 * p ≤ s ^ 2 := by
    dsimp [s, p]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  change p ≤ 2
  by_contra hbad
  have hpos : 0 < (p - 2) * (p + 2 * s + 3) := mul_pos (by linarith) (by linarith)
  nlinarith only [he, hsp, hs2, hpos]
