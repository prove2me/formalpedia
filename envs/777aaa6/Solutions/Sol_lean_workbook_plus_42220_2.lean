-- Prove2me | solution 2 for lean_workbook_plus_42220
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:54.299731+00:00
-- url     : https://prove2.me/submissions/c204d66c-c16a-4fb5-9ac0-97b65460ef5b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℂ} (h : (a - b) * (b - c) * (c - a) = 0) :
  a = b ∨ b = c ∨ c = a := by
  intros
  grind
