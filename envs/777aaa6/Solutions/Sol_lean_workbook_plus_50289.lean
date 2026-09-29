-- Prove2me | solution 1 for lean_workbook_plus_50289
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:32.561568+00:00
-- url     : https://prove2.me/submissions/ddab0642-0358-45b3-bf35-b2c6b067ba09

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (p : ℝ) (hp : p ≠ 0) (hbc : b = -a * (p^4 + 1) / p^3) (hcc : c = a / p^2) : (a^2 + c^2)^2 = a * b^2 * c := by
  intros
  grind
