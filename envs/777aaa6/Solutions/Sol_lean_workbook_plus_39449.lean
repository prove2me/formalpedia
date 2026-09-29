-- Prove2me | solution 1 for lean_workbook_plus_39449
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:59.559994+00:00
-- url     : https://prove2.me/submissions/9c63475b-3c36-4e05-bd7b-513a6ee121eb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y k : ℤ) : (x * y = k * (k + 1) / 2 - x - y) ↔ (x + 1) * (y + 1) = k * (k + 1) / 2 + 1 := by
  intros
  grind
