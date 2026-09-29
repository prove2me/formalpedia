-- Prove2me | solution 1 for NeuralCodeSingletonBound.repetition_attains_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:23:54.857422+00:00
-- url     : https://prove2.me/submissions/6bc598be-d43b-4e38-ae96-45c074534bfc

import Mathlib
import Definitions.Def_Novelty_NeuralCodeSingletonBound
import Definitions.Def_Novelty_NeuralCoding
open NeuralCodeSingletonBound in
theorem solution (N : ℕ) (hN : 1 ≤ N) :
    (∀ x ∈ repetitionCode N, ∀ y ∈ repetitionCode N, x ≠ y → N ≤ hammingDist x y) ∧
    (repetitionCode N).card = 2 ^ (N + 1 - N) := by
  -- the two codewords differ in every coordinate
  have hne : (fun _ : Fin N => false) ≠ (fun _ => true) := fun h => by
    have := congrFun h ⟨0, hN⟩
    simp at this
  have hd : hammingDist (fun _ : Fin N => false) (fun _ => true) = N := by
    simp [hammingDist]
  constructor
  · intro x hx y hy hxy
    simp only [repetitionCode, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · rw [hd]
    · rw [hammingDist_comm, hd]
    · exact absurd rfl hxy
  · rw [repetitionCode, Finset.card_pair hne, show N + 1 - N = 1 by omega]
    rfl
