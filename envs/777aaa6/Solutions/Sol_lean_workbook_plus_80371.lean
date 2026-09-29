-- Prove2me | solution 1 for lean_workbook_plus_80371
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:20:52.924871+00:00
-- url     : https://prove2.me/submissions/134a0f61-7956-4cf9-80c3-78e8e1eb6ade

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ x : ℕ → ℝ, x 0 = 1 ∧ ∀ n, x (n + 1) = x n ^ 2 + 3 / 16 := by
  let x : ℕ → ℝ := fun n => Nat.rec 1 (fun _ xn => xn ^ 2 + 3 / 16) n
  refine ⟨x, rfl, ?_⟩
  intro n
  rfl
