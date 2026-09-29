-- Prove2me | solution 1 for lean_workbook_plus_33786
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:15.324938+00:00
-- url     : https://prove2.me/submissions/57c3b879-ba14-42f6-8bc0-6777a1707330

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c p : ℝ} (h : a + b + c = 2 * p) :
  a * (p - b) * (p - c) * (b ^ 2 - c ^ 2) + b * (p - c) * (p - a) * (c ^ 2 - a ^ 2) +
      c * (p - a) * (p - b) * (a ^ 2 - b ^ 2) = -p ^ 2 * (a - b) * (b - c) * (c - a) := by
  intros
  grind
