-- Prove2me | solution 1 for lean_workbook_plus_24293
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:15.869883+00:00
-- url     : https://prove2.me/submissions/13c0276d-132b-4b96-8965-8e1efc2c51de

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (α β γ δ : ℂ) (p q r s : ℂ)
    (h : α + β + γ + δ = -p)
    (h' : α * β + α * γ + α * δ + β * γ + β * δ + γ * δ = q)
    (h'' : α * β * γ + α * β * δ + α * γ * δ + β * γ * δ = -r)
    (h''' : α * β * γ * δ = s) :
    (α * β + γ * δ) * (β * γ + α * δ) * (γ * α + β * δ) =
      r^2 - 4*q*s + p^2 * s := by
  have hp : p = -(α + β + γ + δ) := by linear_combination h
  have hr : r = -(α * β * γ + α * β * δ + α * γ * δ + β * γ * δ) := by
    linear_combination h''
  rw [hp, hr, ← h', ← h''']
  ring

#print axioms solution
