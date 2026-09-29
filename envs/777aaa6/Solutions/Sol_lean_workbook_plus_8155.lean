-- Prove2me | solution 1 for lean_workbook_plus_8155
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:55.148356+00:00
-- url     : https://prove2.me/submissions/54596455-7e49-4872-87ae-d9af5316afb7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℤ → ℤ) (hf : ∃ a b, ∀ x, f x = a * x + b) : f 0 = 3 ∧ f 1 = 2023 → f (-10) = -20197 := by
  intros
  grind
