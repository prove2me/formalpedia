-- Prove2me | solution 1 for lean_workbook_plus_7595
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:15.539814+00:00
-- url     : https://prove2.me/submissions/299a530f-85c5-4d53-b027-16ed778f90ca

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : a^2 * b + b^2 * c + c^2 * a + a * b * c ≤ 4 ↔ a^2 * b + b^2 * c + c^2 * a ≤ 4 - a * b * c := by
  intros
  grind
