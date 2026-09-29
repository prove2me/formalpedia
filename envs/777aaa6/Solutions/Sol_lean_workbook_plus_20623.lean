-- Prove2me | solution 1 for lean_workbook_plus_20623
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:44.237801+00:00
-- url     : https://prove2.me/submissions/7b84c30d-60c8-4e31-8f63-04bcd5fe53a5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ)
  (h₀ : -b ≤ a)
  (h₁ : b ≤ a) :
  a ≥ |b| := by
  intros
  grind
