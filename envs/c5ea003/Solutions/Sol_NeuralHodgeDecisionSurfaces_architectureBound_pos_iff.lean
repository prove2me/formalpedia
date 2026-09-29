-- Prove2me | solution 1 for NeuralHodgeDecisionSurfaces.architectureBound_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:26:15.199254+00:00
-- url     : https://prove2.me/submissions/cdf89211-5315-408e-bb19-b654b6ebcfee

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










/-! ## The proposed architecture expression -/








/-! ## Machine-checked small cases

These examples serve as concise computational evidence.  They are checked by
Lean's kernel along with the general theorems above. -/

example : architectureBound 2 3 [] 1 1 = 6 := by decide
example : architectureBound 3 4 [2] 1 2 = 36 := by decide
example : architectureBound 4 5 [2, 3] 2 1 = 180 := by decide
example : architectureBound 2 3 [] 3 0 = 0 := by decide



open NeuralHodgeDecisionSurfaces in
theorem solution    {first last p q : ℕ} {interior : List ℕ}
    (hinterior : ∀ w ∈ interior, 0 < w) :
    0 < architectureBound first last interior p q ↔
      p ≤ first ∧ q ≤ last := by
  unfold architectureBound
  have hinterior_pos : 0 < interior.prod := List.prod_pos hinterior
  have mul_pos_iff : ∀ a b : ℕ, 0 < a * b ↔ 0 < a ∧ 0 < b := fun a b => by
    constructor
    · intro h
      constructor
      · by_contra ha; simp [ha] at h
      · by_contra hb; simp [hb] at h
    · exact fun ⟨ha, hb⟩ => Nat.mul_pos ha hb
  rw [mul_pos_iff, mul_pos_iff]
  constructor
  · intro h
    have h1 := h.1.1
    have h2 := h.1.2
    constructor
    · by_contra hp; simp [Nat.choose_eq_zero_of_lt (not_le.mp hp)] at h1
    · by_contra hq; simp [Nat.choose_eq_zero_of_lt (not_le.mp hq)] at h2
  · intro ⟨hp, hq⟩
    exact ⟨⟨Nat.choose_pos hp, Nat.choose_pos hq⟩, hinterior_pos⟩
