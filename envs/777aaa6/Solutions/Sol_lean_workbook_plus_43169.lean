-- Prove2me | solution 1 for lean_workbook_plus_43169
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:45.719207+00:00
-- url     : https://prove2.me/submissions/6d14d003-7200-408c-98c2-cb464dc22473

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ)
  (h₀ : 0 < a)
  (h₁ : (↑52 / a - 1) * 24 + (↑24 / a - 1) * 52 ≤ 1994) :
  a ≥ 416 / 345 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a]
