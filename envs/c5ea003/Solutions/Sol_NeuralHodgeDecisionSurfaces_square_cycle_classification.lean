-- Prove2me | solution 1 for NeuralHodgeDecisionSurfaces.square_cycle_classification
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:26:15.764136+00:00
-- url     : https://prove2.me/submissions/42f51155-f796-4fc0-b460-d874ef9c276a

-- Sol generated from MachineLearning/NeuralHodgeDecisionSurfaces.lean
import Mathlib
import Definitions.Def_MachineLearning_NeuralHodgeDecisionSurfaces
/-
# A finite polyhedral Hodge shadow for ReLU decision surfaces

This file proves two concrete results that remain valid without imposing a
(nonexistent, in general) complex Hodge structure on a real ReLU decision set.

First, the cycle space of the four-edge square is exactly one-dimensional:
every rational 1-cycle is a common multiple of the sum of its four linear
edges.  Thus every class in this small polyhedral model has an explicit
face-supported representative.

Second, we study the proposed architecture-dependent numerical expression
`choose first p * choose last q * product interior`.  We prove its vanishing
range, reversal symmetry, and a uniform exponential estimate.
-/


open scoped BigOperators
open Finset

open NeuralHodgeDecisionSurfaces

/-! ## The square as a finite decision-surface model -/






/-- Boundary cancellation forces all four edge coefficients to agree. -/
theorem square_cycle_coefficients_equal (x : SquareChain) (hx : IsSquareCycle x) :
    x 0 = x 1 ∧ x 1 = x 2 ∧ x 2 = x 3 := by
  simp [IsSquareCycle] at hx
  have h1 : x 0 - x 1 = 0 := by simpa using congr_fun hx 1
  have h2 : x 1 - x 2 = 0 := by simpa using congr_fun hx 2
  have h3 : x 2 - x 3 = 0 := by simpa using congr_fun hx 3
  exact ⟨by linarith, by linarith, by linarith⟩




/-! ## The proposed architecture expression -/








/-! ## Machine-checked small cases

These examples serve as concise computational evidence.  They are checked by
Lean's kernel along with the general theorems above. -/

example : architectureBound 2 3 [] 1 1 = 6 := by decide
example : architectureBound 3 4 [2] 1 2 = 36 := by decide
example : architectureBound 4 5 [2, 3] 2 1 = 180 := by decide
example : architectureBound 2 3 [] 3 0 = 0 := by decide



open NeuralHodgeDecisionSurfaces in
theorem solution(x : SquareChain) :
    IsSquareCycle x ↔ ∃! a : ℚ, x = a • fundamentalSquareCycle := by
  constructor
  · intro hx
    -- Forward: x is a cycle implies x = a • fundamentalSquareCycle for unique a
    have heq := square_cycle_coefficients_equal x hx
    use x 0
    constructor
    · -- Show x = (x 0) • fundamentalSquareCycle
      funext i
      fin_cases i <;> simp [fundamentalSquareCycle, heq]
    · -- Uniqueness
      intro y hy
      have h : x 0 = y := by
        have := congr_fun hy 0
        simp [fundamentalSquareCycle] at this
        linarith
      linarith
  · intro ⟨a, ha, _⟩
    -- Backward: x = a • fundamentalSquareCycle implies x is a cycle
    rw [ha]
    change squareBoundary (a • fundamentalSquareCycle) = 0
    unfold squareBoundary fundamentalSquareCycle
    funext v
    fin_cases v <;> simp
