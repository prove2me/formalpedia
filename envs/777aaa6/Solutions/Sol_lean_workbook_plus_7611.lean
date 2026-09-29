-- Prove2me | solution 1 for lean_workbook_plus_7611
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:56.81276+00:00
-- url     : https://prove2.me/submissions/ee64b6ca-02a0-483d-942a-5bc4455b6100

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℚ) (h₁ : a = 17 / 2) (h₂ : b = 11) (h₃ : c = 1 / 4) : a * b * c = 187 / 8 := by
  intros
  grind
