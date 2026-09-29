-- Prove2me | solution 1 for lean_workbook_plus_60537
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:05.664354+00:00
-- url     : https://prove2.me/submissions/9e9a4dff-6bea-4116-8b7b-21dc9dfeeb31

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} : a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b) ≥ 0 ↔ 6 * a * (a - b) * (a - c) + 6 * b * (b - a) * (b - c) + 6 * c * (c - a) * (c - b) ≥ 0 := by
  intros
  grind
