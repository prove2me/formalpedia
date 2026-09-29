-- Prove2me | solution 1 for lean_workbook_plus_26754
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:30.015879+00:00
-- url     : https://prove2.me/submissions/f54acd8f-d9c2-414f-89e5-82d5ec55fb86

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z: ℝ) : (x^2 + y^2) / 2 ≥ x * y ∧ (x^2 + z^2) / 2 ≥ x * z ∧ (y^2 + z^2) / 2 ≥ y * z := by
  constructor
  · nlinarith only [sq_nonneg (x-y)]
  constructor
  · nlinarith only [sq_nonneg (x-z)]
  · nlinarith only [sq_nonneg (y-z)]
