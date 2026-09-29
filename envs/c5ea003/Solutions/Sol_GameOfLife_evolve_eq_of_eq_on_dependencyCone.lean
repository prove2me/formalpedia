-- Prove2me | solution 1 for GameOfLife.evolve_eq_of_eq_on_dependencyCone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:45:09.081434+00:00
-- url     : https://prove2.me/submissions/5acc3006-67fe-44aa-a05d-bd8bb33c07e5

-- Sol generated from Novelty/GameOfLifeUniversality.lean
import Mathlib
import Definitions.Def_Novelty_GameOfLifeUniversality

/-!
# Conway's Game of Life: local semantics and finite simulation cones

This file gives a self-contained formalization of Conway's rule on `ℤ × ℤ` and a
constructive chain of results about exact local simulation.  The final results prove
that the value of a cell after `t` generations is determined by an explicitly finite
set of initial cells, and bound the size of this dependency cone by `9^t`.

This is foundational infrastructure toward a direct universality proof; it does not
claim the still-missing construction of wires, clocks, and a universal machine.
-/

open GameOfLife













/-- Agreement on the closed neighborhood suffices to determine the next state. -/
theorem step_eq_of_eq_on_closedNeighbors {c d : Config} {p : Cell}
    (h : ∀ q ∈ closedNeighbors p, c q = d q) : step c p = step d p := by
  unfold step
  have hp : c p = d p := h p (Finset.mem_insert_self p (neighbors p))
  have hneighbors : ∀ q ∈ neighbors p, c q = d q := fun q hq => h q (Finset.mem_insert_of_mem hq)
  have hcount : liveNeighborCount c p = liveNeighborCount d p := by
    unfold liveNeighborCount
    apply Finset.sum_congr rfl
    intro q hq
    simp [hneighbors q hq]
  rw [hp, hcount]



/-- Each successive dependency cone is the union of closed neighborhoods of the
previous cone. -/
theorem dependencyCone_succ (t : ℕ) (p : Cell) :
    dependencyCone (t + 1) p = (dependencyCone t p).biUnion closedNeighbors := by
  simp only [dependencyCone]






open GameOfLife in
theorem solution(t : ℕ) {c d : Config} {p : Cell}
    (h : ∀ q ∈ dependencyCone t p, c q = d q) : evolve t c p = evolve t d p := by
  -- Helper: dependency cone subset
  have hsub : ∀ t' r q, q ∈ closedNeighbors r → dependencyCone t' q ⊆ dependencyCone (t' + 1) r := by
    refine fun t' => Nat.rec ?_ ?_ t'
    · intro r q hq; simp [dependencyCone]; exact hq
    · intro t'' ht'' r q hq
      rw [dependencyCone_succ, dependencyCone_succ]
      apply Finset.biUnion_subset.mpr
      intro s hs
      apply Finset.subset_biUnion_of_mem
      exact ht'' r q hq hs
  -- Generalize to all cells at once
  have hgen : ∀ t, ∀ r, (∀ q ∈ dependencyCone t r, c q = d q) → evolve t c r = evolve t d r := by
    refine fun t => Nat.rec ?_ ?_ t
    · intro r hr; simp [dependencyCone] at hr; simpa [evolve] using hr
    · intro t' ih r hr
      simp only [evolve, Function.iterate_succ_apply']
      apply step_eq_of_eq_on_closedNeighbors
      intro q hq
      apply ih
      intro s hs
      exact hr s (hsub t' r q hq hs)
  exact hgen t p h
