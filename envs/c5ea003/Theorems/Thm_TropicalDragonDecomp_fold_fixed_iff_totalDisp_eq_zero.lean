-- Prove2me | Theorems.Thm_TropicalDragonDecomp_fold_fixed_iff_totalDisp_eq_zero
-- name    : TropicalDragonDecomp.fold_fixed_iff_totalDisp_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:09.774722+00:00
-- url     : https://prove2.me/theorems/ad60d44a-353f-4023-a601-2cea56f5c1b5
-- title:
--   A turn sequence returns the walker to its starting position
-- statement:
--   A turn sequence returns the walker to its starting position
--   if and only if the total displacement is zero.
--
--   ```lean
--   theorem TropicalDragonDecomp.fold_fixed_iff_totalDisp_eq_zero(s : WalkState) (turns : List Bool) :
--       (turns.foldl applyStep s).pos = s.pos ↔ totalDisp s.dir turns = (0, 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalDragonDecomposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalDragonDecomposition.lean#L198

-- Thm stub generated from Algebra/TropicalDragonDecomposition.lean
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



/-! ### Main Decomposition Theorem -/



/-! ### Additive Structure of Displacement -/



/-! ### Orbit Classification -/


/-! ### Periodicity Criterion -/

theorem TropicalDragonDecomp.fold_fixed_iff_totalDisp_eq_zero(s : WalkState) (turns : List Bool) :
    (turns.foldl applyStep s).pos = s.pos ↔ totalDisp s.dir turns = (0, 0) := by sorry
