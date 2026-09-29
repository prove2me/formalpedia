-- Prove2me | solution 1 for TropicalDragonDecomp.fold_fixed_iff_totalDisp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:08:23.794334+00:00
-- url     : https://prove2.me/submissions/84bd6384-5386-4f92-beb5-8ac8b858e171

-- Sol generated from Algebra/TropicalDragonDecomposition.lean
import Mathlib
import Definitions.Def_Algebra_TropicalDragonDecomposition

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

open TropicalDragonDecomp

/-! ### Core Definitions -/






/-! ### Direction Sequence -/





/-! ### Displacement: Recursive Definition -/




/-! ### The Direction After a Word -/




/-! ### Helper: step properties -/



lemma step_displacement (s : WalkState) (t : Bool) :
    (applyStep s t).pos
      = (s.pos.1 + (dirVec s.dir).1, s.pos.2 + (dirVec s.dir).2) := rfl

lemma step_dir (s : WalkState) (t : Bool) :
    (applyStep s t).dir = turnDir s.dir t := rfl

lemma totalDisp_cons (d : Dir) (t : Bool) (ts : List Bool) :
    totalDisp d (t :: ts)
      = ((dirVec d).1 + (totalDisp (turnDir d t) ts).1,
         (dirVec d).2 + (totalDisp (turnDir d t) ts).2) := rfl

/-! ### Main Decomposition Theorem -/

/-- **Main Theorem**: The position after folding a sequence of turns
equals the initial position plus the total displacement.

This is the directional decomposition theorem: a complex iterated
dynamical system on ℤ² decomposes into an additive accumulation of
local directional translations. -/
theorem foldl_applyStep_eq_add_totalDisp (s : WalkState) (turns : List Bool) :
    (turns.foldl applyStep s).pos =
    (s.pos.1 + (totalDisp s.dir turns).1, s.pos.2 + (totalDisp s.dir turns).2) := by
  induction turns generalizing s with
  | nil => simp [totalDisp]
  | cons t ts ih =>
    simp only [foldl_cons]
    rw [ih]
    simp only [step_displacement, step_dir, totalDisp_cons]
    ext <;> ring


/-! ### Additive Structure of Displacement -/



/-! ### Orbit Classification -/


/-! ### Periodicity Criterion -/


/-! ### Existential Form -/


/-! ### Singleton and Two-Step Composition -/



/-! ### Direction Vector Finset Decomposition -/


/-
Total displacement decomposes as a weighted sum over direction multiplicities:
the displacement equals the sum over all directions of
(count of that direction) × (direction vector).
-/



open TropicalDragonDecomp in
theorem solution(s : WalkState) (turns : List Bool) :
    (turns.foldl applyStep s).pos = s.pos ↔ totalDisp s.dir turns = (0, 0) := by
  rw [foldl_applyStep_eq_add_totalDisp]
  constructor
  · intro h
    have h1 := congr_arg Prod.fst h
    have h2 := congr_arg Prod.snd h
    simp at h1 h2
    ext <;> omega
  · intro h
    have h1 := congr_arg Prod.fst h
    have h2 := congr_arg Prod.snd h
    simp at h1 h2
    ext <;> omega
