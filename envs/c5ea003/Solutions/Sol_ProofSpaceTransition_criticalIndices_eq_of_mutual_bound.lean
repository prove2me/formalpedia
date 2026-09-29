-- Prove2me | solution 1 for ProofSpaceTransition.criticalIndices_eq_of_mutual_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:11:25.823698+00:00
-- url     : https://prove2.me/submissions/80e4d1bc-cf74-4426-b873-6f487c0c4cb0

-- Sol generated from Shared/StableProofSpaceTransitions.lean
import Mathlib

/-!
# Stability of Critical Indices Under Bounded Recodings

This file develops an abstract sharp-transition theorem for real-valued order
parameters.  An antitone profile converging to zero has a unique last index at
or above every positive level that is attained initially.  Two such profiles
whose shifted values bound one another have critical indices differing by at
most the shift.  Thus a finite-distortion recoding cannot move a sharp
transition by more than its distortion bound.
-/


open Filter Topology






theorem solution    (p q : ℕ → ℝ) (ε : ℝ) (cp cq : ℕ)
    (hp : ∀ n, p n < ε ↔ cp < n)
    (hq : ∀ n, q n < ε ↔ cq < n)
    (hpq : ∀ n, p n ≤ q n)
    (hqp : ∀ n, q n ≤ p n) :
    cp = cq := by
  have hpq_eq : ∀ n, p n = q n := fun n => le_antisymm (hpq n) (hqp n)
  suffices cp ≥ cq ∧ cq ≥ cp by exact le_antisymm this.2 this.1
  constructor
  · by_contra h
    push_neg at h
    have hpcq : p cq < ε := (hp cq).mpr h
    have hqce : ¬(q cq < ε) := by
      rw [hq]
      exact lt_irrefl cq
    linarith [hpq_eq cq]
  · by_contra h
    push_neg at h
    have hqcp : q cp < ε := (hq cp).mpr h
    have hpce : ¬(p cp < ε) := by
      rw [hp]
      exact lt_irrefl cp
    linarith [hpq_eq cp]
