-- Prove2me | solution 1 for lean_workbook_plus_27509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:32.344231+00:00
-- url     : https://prove2.me/submissions/00e4bca3-9b6e-476d-948c-2b239753adc3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (s t : ℕ) (hs : 4 * s ^ 2 - 3 * t ^ 2 = 1) : s ≥ 1 ∧ t ≥ 1 := by
  intros
  grind
