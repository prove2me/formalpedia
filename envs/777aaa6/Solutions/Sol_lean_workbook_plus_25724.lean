-- Prove2me | solution 1 for lean_workbook_plus_25724
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:25.551194+00:00
-- url     : https://prove2.me/submissions/68a8d67b-7e17-4c97-b168-265d327b7677

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∃ f : ℕ → ℕ, f 2008 ≠ 2008 ∧ ∀ m n, f (m + f n) = f (f m) + f n := by
  intros
  refine ⟨0, ?_⟩ <;> norm_num at *
