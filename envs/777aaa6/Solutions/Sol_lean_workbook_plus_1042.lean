-- Prove2me | solution 1 for lean_workbook_plus_1042
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:17.459648+00:00
-- url     : https://prove2.me/submissions/999aada0-989c-486d-975e-1931d2d15ab7

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (¬∃ f : ℕ → ℕ, ∀ n, f (f n) = f (n + 1) - f n) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
