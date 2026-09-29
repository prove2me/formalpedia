-- Prove2me | solution 1 for lean_workbook_plus_72962
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:12:51.764009+00:00
-- url     : https://prove2.me/submissions/41ecfe32-86c9-41e8-bf91-6f85b7a7196a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {x a : ℝ} (h₁ : x ≠ 0) (h₂ : a = 7) : (x + a + 1) / x = a - x ↔ x^2 - (a - 1) * x + a + 1 = 0 := by
  clear h₂
  field_simp
  constructor <;> intro h <;> nlinarith only [h]
