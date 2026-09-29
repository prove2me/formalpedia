-- Prove2me | solution 1 for lean_workbook_plus_59114
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:09.227137+00:00
-- url     : https://prove2.me/submissions/b46ceed5-8d7c-451b-bc7d-84fa62c750f3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (u m : ℝ) (t : ℝ → ℝ) (hf : ∀ x, f (2 * x + m) = 2 * f x + u) (ht : ∀ x, t x = f (x - m) + u) : ∀ x, t (2 * x) = 2 * t x := by
  intros
  grind
