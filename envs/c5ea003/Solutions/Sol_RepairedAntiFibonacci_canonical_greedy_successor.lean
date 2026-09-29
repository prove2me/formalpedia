-- Prove2me | solution 1 for RepairedAntiFibonacci.canonical_greedy_successor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:23:35.95813+00:00
-- url     : https://prove2.me/submissions/d330edf1-4c12-401b-8ab4-d2057bfbbc9e

-- Sol generated from Logic/RepairedAntiFibonacciClassification.lean
import Mathlib
import Definitions.Def_Logic_RepairedAntiFibonacciClassification

/-!
# Classification of the repaired anti-Fibonacci process

The global additive repair from `Novelty.RepairedAntiFibonacci` is not merely
well-defined and increasing: its trajectory is forced exactly.  Starting from
one, the greedy process enumerates the positive odd integers.

The key point is that sums of earlier odd values are even.  At stage `n`, the
next odd value `2n+3` is therefore admissible, while the only smaller candidate
above `2n+1`, namely `2n+2`, is already the sum of the first and current values.
This gives both existence and uniqueness, and turns the earlier exponential
one-step ceiling into an exact linear law.
-/

open RepairedAntiFibonacci

noncomputable section





/-- Membership in the restricted sumset has the expected witness form. -/
lemma mem_priorPairSums_iff {a : ℕ → ℕ} {n s : ℕ} :
    s ∈ priorPairSums a n ↔ ∃ i < n, ∃ j < n, a i + a j = s := by
  simp only [priorPairSums, Finset.mem_image, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, heq⟩
    exact ⟨i, hi, j, hj, heq⟩
  · rintro ⟨i, hi, j, hj, heq⟩
    exact ⟨⟨i, j⟩, ⟨hi, hj⟩, heq⟩







/-- At every stage, the next positive odd integer is admissible for the odd
history. -/
theorem canonical_next_admissible (n : ℕ) :
    AdmissibleAfter canonical n (canonical (n + 1)) := by
  constructor
  · simp [canonical]
  · rw [mem_priorPairSums_iff]
    rintro ⟨i, hi, j, hj, heq⟩
    simp only [canonical] at heq
    omega












open RepairedAntiFibonacci in
theorem solution(n : ℕ) :
    IsGreedySuccessor canonical n (canonical (n + 1)) := by
  refine ⟨canonical_next_admissible n, ?_⟩
  intro w hw
  by_contra hnot
  have hbetween : canonical n < w := hw.1
  have hwsmall : w < canonical (n + 1) := by omega
  simp only [canonical] at hbetween hwsmall
  have hweq : w = canonical 0 + canonical n := by
    simp only [canonical]
    omega
  apply hw.2
  rw [mem_priorPairSums_iff]
  exact ⟨0, by omega, n, by omega, hweq.symm⟩
