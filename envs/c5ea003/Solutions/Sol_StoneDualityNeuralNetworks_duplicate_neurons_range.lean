-- Prove2me | solution 1 for StoneDualityNeuralNetworks.duplicate_neurons_range
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:48:55.890653+00:00
-- url     : https://prove2.me/submissions/609b22c1-f747-4dd4-b314-8ab0d380649c

-- Sol generated from Logic/StoneDualityNeuralNetworks.lean
import Mathlib
import Definitions.Def_Logic_StoneDualityNeuralNetworks

/-!
# Stone duality and neural classifiers: precise positive results and counterexamples

A classifier induces a Boolean algebra of observable predicates, but several stronger
claims in the proposed framing fail.  This file isolates the failures without assuming
any particular implementation of neural networks.
-/

open StoneDualityNeuralNetworks




















open StoneDualityNeuralNetworks in
theorem solution:
    Set.range (activationVector (k := 2) (fun _ => 0)) =
      {p | p = (fun _ => false) ∨ p = (fun _ => true)} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : 0 < x
    · right
      funext i
      simp [activationVector, hx]
    · left
      funext i
      simp [activationVector, hx]
  · intro hp
    rcases hp with rfl | rfl
    · refine ⟨0, ?_⟩
      funext i
      simp [activationVector]
    · refine ⟨1, ?_⟩
      funext i
      simp [activationVector]
