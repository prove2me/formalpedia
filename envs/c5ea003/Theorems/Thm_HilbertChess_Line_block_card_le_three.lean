-- Prove2me | Theorems.Thm_HilbertChess_Line_block_card_le_three
-- name    : HilbertChess.Line.block_card_le_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:23:19.521039+00:00
-- url     : https://prove2.me/theorems/13e83f77-3718-47e2-89bc-a9ebc47d4100
-- title:
--   **Any single long-range piece covers at most `3` of the `9` squares of a
-- statement:
--   **Any single long-range piece covers at most `3` of the `9` squares of a
--   king's neighbourhood.**  A line hits each of the three rows (or, if horizontal,
--   each of the three columns) at most once.
--
--   ```lean
--   theorem HilbertChess.Line.block_card_le_three(L : Line) (p : Square) :
--       (L.blockCovered p).card ≤ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HilbertChessLines.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HilbertChessLines.lean#L127

-- Thm stub generated from Geometry/HilbertChessLines.lean
import Mathlib
import Definitions.Def_Geometry_HilbertChessLines
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Infinite-board chess: the sharp line-covering threshold for checkmate

We play chess on the **Hilbert board** `ℤ × ℤ`.  The pieces of interest are the
*long-range* pieces — rooks, bishops and queens — each of whose reach along a
single ray is an **affine line**

```
{ (x, y) | a * x + b * y = c }   with (a, b) ≠ (0, 0).
```

Modelling every long-range attacker as such a `Line` covers all of them at once:
a rook is a horizontal (`a = 0`) or vertical (`b = 0`) line, a bishop is a
diagonal (`a = ±1, b = ∓1`) line, a queen is either, and in fact *any* straight
ray in any direction is included.

This generality is what distinguishes the development here from an axis-parallel
(rook-only) treatment: we obtain a **sharp threshold** for how many long-range
pieces are needed to trap a king, valid for arbitrary line directions.

## The chain of results

Each result feeds the next.

1. `Line.covered_snd_injOn` / `Line.covered_fst_injOn` — a line is functional in
   one coordinate: fixing the other coordinate pins the point down.
2. `Line.block_card_le_three` — **any single line covers at most `3` of the `9`
   squares of a king's `3 × 3` neighbourhood.**  (Uses 1.)
3. `blockCovered_card_le` — a configuration of `n` lines covers at most `3 * n`
   of those `9` squares.  (Uses 2, by induction on the list.)
4. `no_mate_with_lt_three` — **fewer than three long-range pieces can never
   checkmate a king**: the king always keeps a safe square in its neighbourhood.
   (Uses 3; `9 > 3 * 2`.)
5. `mate_exists` — **three pieces suffice**: three parallel rooks explicitly
   checkmate a king, so the threshold `3` is sharp.  (Independent construction.)
6. `covers_row_finite`, `attacked_row_finite`, `exists_safe_row`,
   `escape_infinite`, `escape_unbounded` — globally, any finite configuration
   leaves a whole cofinite family of safe squares, so the lone king can always
   flee arbitrarily far: the board is never fully covered.  (Uses 1.)
-/

open HilbertChess








/-! ## The king's `3 × 3` neighbourhood -/





/-- The offsets a single line covers, relative to a center `p`. -/
def Line.blockCovered (L : Line) (p : Square) : Finset Square :=
  blockOffsets.filter (fun d => L.covers (p.1 + d.1, p.2 + d.2))


/-! ## Step 1: a line is functional in one coordinate -/



/-! ## Step 2: one line covers at most 3 of the 9 neighbourhood squares -/

theorem HilbertChess.Line.block_card_le_three(L : Line) (p : Square) :
    (L.blockCovered p).card ≤ 3 := by sorry
