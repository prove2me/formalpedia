-- Prove2me | solution 1 for lean_workbook_plus_69810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:22.447922+00:00
-- url     : https://prove2.me/submissions/2f502914-dbf7-438f-8200-056aac304b88

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ^ 2-b ^ 2 = b*c) (hbc : b ^ 2-c ^ 2 = a*c) : a ^ 2-c ^ 2 = a*b := by
  intros
  grind
