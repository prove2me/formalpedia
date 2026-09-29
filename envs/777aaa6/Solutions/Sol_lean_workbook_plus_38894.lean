-- Prove2me | solution 1 for lean_workbook_plus_38894
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:16.684605+00:00
-- url     : https://prove2.me/submissions/d9736754-51b6-476e-9fb1-019eede3758a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1) : 1 / (p * (p + 1)) + 1 / (q * (q + 1)) ≥ 1 / 3 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg (p - q)]
