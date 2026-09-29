-- Prove2me | solution 1 for lean_workbook_plus_23509
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:48:00.483538+00:00
-- url     : https://prove2.me/submissions/6a792607-565b-4e1c-b94b-7be3a002127f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (α : ℝ) (α_pos : 0 < α) : ∃ a : ℕ → ℝ, a 0 = α ∧ ∀ n, a (n + 1) = a n / (1 + a n) := by
  have hd (n : ℕ) : 0 < 1+(n : ℝ)*α := by positivity
  refine ⟨fun n => α/(1+(n : ℝ)*α),by simp,?_⟩
  intro n
  have hnext : 1+((n : ℝ)+1)*α ≠ 0 := by positivity
  have hr : 1+α/(1+(n : ℝ)*α) ≠ 0 := by positivity
  push_cast
  field_simp [ne_of_gt (hd n),hnext,hr]
  <;> ring
