-- Prove2me | solution 1 for lean_workbook_plus_49780
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:40.685264+00:00
-- url     : https://prove2.me/submissions/4f58c783-a5f5-4849-af1a-9318ef00840b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (b : ℕ) (v : ℕ → ℕ) (h₁ : b ≥ 2) (h₂ : v 0 = 0) (h₃ : v 1 = 0) (h₄ : ∀ i, v (i + 2) = b * v (i + 1) - v i) : ∀ i, v i = 0 := by
  apply Nat.twoStepInduction (P := fun i => v i=0) h₂ h₃
  intro i hi hi1
  rw [h₄,hi,hi1]
  simp
