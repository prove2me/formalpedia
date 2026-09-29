-- Prove2me | Definitions.Def_Algebra_TropicalDragonDecomposition
-- name    : Algebra_TropicalDragonDecomposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:15:36.692447+00:00
-- url     : https://prove2.me/theorems/3f02321a-3a2c-47fe-b7f8-0ebedcea975b
-- title:
--   Aether Catalog definitions — Algebra_TropicalDragonDecomposition
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalDragonDecomposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalDragonDecomposition.lean by skeleton subtraction
import Mathlib

/-!
# Directional Decomposition for Tropical Dragon Dynamics

This file establishes a **directional decomposition theorem** for the tropical dragon
curve dynamics: any finite word of turns decomposes into an additive accumulation of
local directional translations.

## Mathematical Overview

The Heighway dragon curve walker moves on ℤ² with a facing direction from `Fin 4`
(East/North/West/South). At each step, it advances one unit in its current direction,
then turns left or right. The key insight is that the position update at each step
is a pure translation determined by the current facing direction.

**Main Theorem** (`foldl_applyStep_eq_add_totalDisp`): For any initial walker state
and any finite sequence of turns, the final position equals the initial position plus
the sum of direction vectors along the path. The direction sequence is entirely
determined by the initial facing direction and the turn sequence.

This decomposes a complex iterated dynamical system into:
1. A **finite-state automaton** (direction evolution, determined by turns),
2. An **additive accumulator** (position = sum of direction vectors).

## Significance

- Turns symbolic dynamics into additive invariants over ℤ².
- Enables orbit classification: two turn sequences produce the same displacement
  iff their accumulated direction-vector sums agree.
- Periodicity reduces to vanishing displacement.
- Opens a pathway to tropical/idempotent finite-generation analysis.

## Main Results

* `step_displacement` — each step translates position by the current direction vector
* `foldl_applyStep_eq_add_totalDisp` — the main decomposition theorem
* `totalDisp_append` — displacement is additive under word concatenation
* `fold_fixed_iff_totalDisp_eq_zero` — periodicity ↔ zero displacement
* `fold_eq_of_totalDisp_eq` — equal displacement ⇒ equal orbit action
* `totalDisp_as_weighted_sum` — displacement decomposes over direction multiplicities
-/

open List Finset

namespace TropicalDragonDecomp

/-! ### Core Definitions -/

/-- Direction on the integer lattice, encoded as `Fin 4`.
0 = East, 1 = North, 2 = West, 3 = South. -/
abbrev Dir := Fin 4

/-- Unit displacement vector for each cardinal direction. -/
def dirVec : Dir → ℤ × ℤ
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (-1, 0)
  | ⟨3, _⟩ => (0, -1)

/-- Walker state: current position on ℤ² and facing direction. -/
structure WalkState where
  pos : ℤ × ℤ
  dir : Dir
  deriving DecidableEq, Repr

/-- Apply a single step: move one unit in the current direction,
then turn right (if `true`) or left (if `false`).
Right turn = `(d + 3) mod 4`, left turn = `(d + 1) mod 4`. -/
def applyStep (s : WalkState) (turn : Bool) : WalkState :=
  { pos := (s.pos.1 + (dirVec s.dir).1, s.pos.2 + (dirVec s.dir).2),
    dir := if turn then (s.dir + 3 : Fin 4) else (s.dir + 1 : Fin 4) }

/-- Update direction after a turn. -/
def turnDir (d : Dir) (turn : Bool) : Dir :=
  if turn then (d + 3 : Fin 4) else (d + 1 : Fin 4)

/-! ### Direction Sequence -/

/-- The sequence of facing directions visited during a walk,
given an initial direction and a list of turns.
The list has the same length as `turns`: one direction per step. -/
def visitedDirs : Dir → List Bool → List Dir
  | _, [] => []
  | d, t :: ts => d :: visitedDirs (turnDir d t) ts




/-! ### Displacement: Recursive Definition -/

/-- Total displacement from a sequence of turns starting at direction `d`.
Defined recursively: empty word gives zero, cons adds the current direction vector. -/
def totalDisp : Dir → List Bool → ℤ × ℤ
  | _, [] => (0, 0)
  | d, t :: ts =>
    let rest := totalDisp (turnDir d t) ts
    ((dirVec d).1 + rest.1, (dirVec d).2 + rest.2)



/-! ### The Direction After a Word -/

/-- The direction after processing a sequence of turns. -/
def finalDir : Dir → List Bool → Dir
  | d, [] => d
  | d, t :: ts => finalDir (turnDir d t) ts



/-! ### Helper: step properties -/



/-! ### Main Decomposition Theorem -/



/-! ### Additive Structure of Displacement -/



/-! ### Orbit Classification -/


/-! ### Periodicity Criterion -/


/-! ### Existential Form -/


/-! ### Singleton and Two-Step Composition -/



/-! ### Direction Vector Finset Decomposition -/

/-- Count of direction `d'` in the visited direction sequence. -/
def dirCount (d : Dir) (turns : List Bool) (d' : Dir) : ℕ :=
  ((visitedDirs d turns).filter (· = d')).length

/-
Total displacement decomposes as a weighted sum over direction multiplicities:
the displacement equals the sum over all directions of
(count of that direction) × (direction vector).
-/


end TropicalDragonDecomp


