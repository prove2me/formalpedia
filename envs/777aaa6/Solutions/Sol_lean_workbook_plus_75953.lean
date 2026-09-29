-- Prove2me | solution 1 for lean_workbook_plus_75953
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:44.371631+00:00
-- url     : https://prove2.me/submissions/a1a0cc0b-301d-43d1-b92f-7c237f7546a9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (p q r : ℝ) (hp : 0 < p ∧ p < 1) (hq : 0 < q ∧ q < 1) (hr : 0 < r ∧ r < 1) : p*q + q*r + r*p - 2*p*q*r < 1 := by
  have h1p : 0<1-p := by linarith [hp.2]
  have h1q : 0<1-q := by linarith [hq.2]
  have h1r : 0<1-r := by linarith [hr.2]
  have hm := mul_pos h1p hq.1
  have hpq : 0<1-p*q := by nlinarith only [hm,hq.2]
  have hA := mul_pos h1r hpq
  have hB := mul_pos hr.1 (mul_pos h1p h1q)
  nlinarith only [hA,hB]
