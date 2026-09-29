-- Prove2me | solution 1 for lean_workbook_plus_74356
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:18.70537+00:00
-- url     : https://prove2.me/submissions/4d373cde-6f57-4e6d-a785-98298e0f4746

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (f g : ℝ → ℝ) (hf : f = fun x => 4*x-2) (hg : g = fun x => 5*x+3) : f (g (f (g x))) = 20 ↔ x = -19/40 := by
  intros
  grind
