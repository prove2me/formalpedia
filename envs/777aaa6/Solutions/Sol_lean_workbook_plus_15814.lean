-- Prove2me | solution 1 for lean_workbook_plus_15814
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T23:15:05.17506+00:00
-- url     : https://prove2.me/submissions/115111b0-48dd-4b32-a6a9-383c8f4f1916

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = -x^3 + a * x^2 + b * x + c)
  (h₁ : a = 6)
  (h₂ : b = -45 / 4)
  (h₃ : c = 13 / 2)
  (h₄ : ∀ x, f x = -(x - 2)^3 + (3 / 4) * (x - 2)), ∃ x, (f x = 0 ∧ 0 < x ∧ x < 1)) := by
  let f : ℝ → ℝ := fun x => -(x-2)^3+(3/4)*(x-2)
  have h0 : ∀ x, f x = -x^3+6*x^2+(-45/4)*x+13/2 := by intro x; dsimp [f]; ring
  have h4 : ∀ x, f x = -(x-2)^3+(3/4)*(x-2) := by intro x; rfl
  intro h
  rcases h 6 (-45/4) (13/2) f h0 rfl rfl rfl h4 with ⟨x,hz,hx0,hx1⟩
  rw [h4] at hz
  have hp : (x-2)*((x-2)^2-3/4)=0 := by nlinarith only [hz]
  rcases mul_eq_zero.mp hp with hleft | hright
  · linarith only [hleft,hx1]
  · nlinarith only [hright,hx1,sq_nonneg (x-1)]
