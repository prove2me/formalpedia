-- Prove2me | solution 1 for lean_workbook_plus_333
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:56.969567+00:00
-- url     : https://prove2.me/submissions/cb01e5e1-a145-4ec5-8c8b-ca446a80cab8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (c : ℂ) (f : ℂ → ℂ) (hf: f c = 0) (h : c * (c + 1) = 0) : c = 0 ∨ c = -1 := by
  intros
  grind
