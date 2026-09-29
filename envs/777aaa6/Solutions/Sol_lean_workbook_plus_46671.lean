-- Prove2me | solution 1 for lean_workbook_plus_46671
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:29.248514+00:00
-- url     : https://prove2.me/submissions/5f165412-a97d-4d92-a02d-77c3720179b8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p q x y : ℝ) (h₁ : x - y = p) (h₂ : x + y = q) (h₃ : p * q = 240) (h₄ : p ≤ q) : x = (q + p) / 2 ∧ y = (q - p) / 2 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
