-- Prove2me | solution 2 for lean_workbook_plus_66346
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:15.527766+00:00
-- url     : https://prove2.me/submissions/79b35c9e-81a5-4344-9c1d-81885dfe40e4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (h : n > 0) : Even (2 ^ n) := by
  intros
  grind
