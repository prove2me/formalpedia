-- Prove2me | solution 1 for lean_workbook_plus_67291
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:53:06.243131+00:00
-- url     : https://prove2.me/submissions/bd860d54-ccda-4889-b327-9ff33174a0ed

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem positive_pair_form (A B C : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hdet : B ^ 2 < A * C) : 0 < A + 2 * B + C := by
  by_contra hn
  have hp := mul_nonneg (show 0 ≤ -(A + 2 * B + C) by linarith)
    (show 0 ≤ A + C - 2 * B by linarith)
  nlinarith [sq_nonneg (A - C)]

theorem quantitative_coefficient_bound (a b c d e : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hb : b ^ 2 ≤ 3 * a * c)
    (h : a / 2008 + b / 2007 + c / 2006 + d / 2005 + e / 2004 = 0) :
    -e / 2004 < a + b + c + d + e := by
  have hdet : (b / 2007) ^ 2 < (3 * a / 2008) * (c / 2006) := by
    nlinarith [mul_pos ha hc]
  have hw := positive_pair_form (3 * a / 2008) (b / 2007) (c / 2006)
    (by linarith) (by linarith) hdet
  linarith only [hw, h]

theorem solution (a b c d e : ℝ) (ha : 0 < a) (he : e < 0)
    (hb : b ^ 2 < 8 / 3 * a * c)
    (habcde : a / 2008 + b / 2007 + c / 2006 + d / 2005 + e / 2004 = 0) :
    a + b + c + d + e > 0 := by
  have hac : 0 < a * c := by nlinarith [sq_nonneg b]
  have hc : 0 < c := (mul_pos_iff_of_pos_left ha).1 hac
  have hb' : b ^ 2 ≤ 3 * a * c := by nlinarith
  have hq := quantitative_coefficient_bound a b c d e ha hc hb' habcde
  linarith
