-- Prove2me | solution 1 for lean_workbook_plus_139
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:39:43.05386+00:00
-- url     : https://prove2.me/submissions/e0d37017-c741-4a78-8f08-4e04a7df317d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution :
  ∀ m n, m % n = 0 → ∃ x, m = n * x := by
  intro m n h
  exact Nat.dvd_of_mod_eq_zero h
