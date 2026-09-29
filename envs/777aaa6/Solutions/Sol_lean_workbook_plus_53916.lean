-- Prove2me | solution 1 for lean_workbook_plus_53916
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:53.588905+00:00
-- url     : https://prove2.me/submissions/694de86c-7a0b-4410-a1fa-67b75918d68a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℂ} : (a + b) * (b + c) * (c + a) = 0 ↔ a = -b ∨ b = -c ∨ c = -a := by
  intros
  grind
