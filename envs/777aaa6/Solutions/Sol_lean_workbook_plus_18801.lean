-- Prove2me | solution 1 for lean_workbook_plus_18801
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:47:04.407991+00:00
-- url     : https://prove2.me/submissions/bc08c05a-56e5-45d8-a42c-cb959da208cd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p q r : ℝ) (h : {p,q,r} ⊆ Set.Ioi 0) (hpqr : p * q * r = 1) (hq2 : q^2 ≥ p * r) (hr2 : r^2 ≥ p * q) : √(q * r) ≥ p := by
  clear hpqr
  have hp : 0 < p := h (by simp)
  have hq : 0 < q := h (by simp)
  have hr : 0 < r := h (by simp)
  have hprod := mul_le_mul hq2 hr2 (le_of_lt (mul_pos hp hq)) (sq_nonneg q)
  have hcancel : p^2*(q*r) ≤ (q*r)*(q*r) := by nlinarith only [hprod]
  apply Real.le_sqrt_of_sq_le
  exact le_of_mul_le_mul_right hcancel (mul_pos hq hr)
