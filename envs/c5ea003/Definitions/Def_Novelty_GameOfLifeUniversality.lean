-- Prove2me | Definitions.Def_Novelty_GameOfLifeUniversality
-- name    : Novelty_GameOfLifeUniversality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:01.391504+00:00
-- url     : https://prove2.me/theorems/0dab9c3f-5354-4417-b9ac-ce4ebe98ef99
-- title:
--   Aether Catalog definitions — Novelty_GameOfLifeUniversality
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.GameOfLifeUniversality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/GameOfLifeUniversality.lean by skeleton subtraction
import Mathlib

/-!
# Conway's Game of Life: local semantics and finite simulation cones

This file gives a self-contained formalization of Conway's rule on `ℤ × ℤ` and a
constructive chain of results about exact local simulation.  The final results prove
that the value of a cell after `t` generations is determined by an explicitly finite
set of initial cells, and bound the size of this dependency cone by `9^t`.

This is foundational infrastructure toward a direct universality proof; it does not
claim the still-missing construction of wires, clocks, and a universal machine.
-/

namespace GameOfLife

abbrev Cell := ℤ × ℤ
abbrev Config := Cell → Bool

/-- The eight cells in the Moore neighborhood. -/
def neighbors (p : Cell) : Finset Cell :=
  { (p.1 - 1, p.2 - 1), (p.1 - 1, p.2), (p.1 - 1, p.2 + 1),
    (p.1, p.2 - 1),                     (p.1, p.2 + 1),
    (p.1 + 1, p.2 - 1), (p.1 + 1, p.2), (p.1 + 1, p.2 + 1) }

/-- The closed Moore neighborhood, including the cell itself. -/
def closedNeighbors (p : Cell) : Finset Cell := insert p (neighbors p)

/-- Number of live Moore neighbors. -/
def liveNeighborCount (c : Config) (p : Cell) : ℕ :=
  ∑ q ∈ neighbors p, (c q).toNat

/-- Conway's B3/S23 local rule. -/
def lifeRule (currentlyAlive : Bool) (n : ℕ) : Bool :=
  decide (n = 3 ∨ (currentlyAlive = true ∧ n = 2))

/-- One synchronous generation of Conway's Game of Life. -/
def step (c : Config) : Config := fun p => lifeRule (c p) (liveNeighborCount c p)

/-- Evolution for exactly `t` generations. -/
def evolve (t : ℕ) (c : Config) : Config := step^[t] c







/-- The explicit finite set of initial cells inspected by the recursive simulator. -/
def dependencyCone : ℕ → Cell → Finset Cell
  | 0, p => {p}
  | t + 1, p => (dependencyCone t p).biUnion closedNeighbors







end GameOfLife


