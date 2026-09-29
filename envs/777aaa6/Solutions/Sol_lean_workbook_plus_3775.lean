-- Prove2me | solution 1 for lean_workbook_plus_3775
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:02.514039+00:00
-- url     : https://prove2.me/submissions/a5dbfa6a-8237-4ede-a5e1-5b84366d327a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ)
  (a : ℕ → ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ i, 0 < i → a i ≥ a (i + 1)) :
  ∀ i, 0 < i → a i - 1 ≥ a (i + 1) - 1 := by
  intros
  grind
