-- Prove2me | Definitions.Def_Geometry_HilbertChessLines
-- name    : Geometry_HilbertChessLines
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:40.555008+00:00
-- url     : https://prove2.me/theorems/6721d5fd-2102-47ca-bf6e-69ad82945987
-- title:
--   Aether Catalog definitions — Geometry_HilbertChessLines
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HilbertChessLines`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HilbertChessLines.lean by skeleton subtraction
import Mathlib
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

namespace HilbertChess

/-- A square of the infinite (Hilbert) chessboard: the integer lattice `ℤ × ℤ`. -/
abbrev Square := ℤ × ℤ

/-- A long-range attacker — rook, bishop or queen ray — modelled by the affine
line `{ (x, y) | a * x + b * y = c }`, required non-degenerate `(a, b) ≠ 0`. -/
structure Line where
  a : ℤ
  b : ℤ
  c : ℤ
  nondeg : a ≠ 0 ∨ b ≠ 0

/-- The square `q` lies on (is attacked along) the line `L`. -/
def Line.covers (L : Line) (q : Square) : Prop := L.a * q.1 + L.b * q.2 = L.c

instance (L : Line) (q : Square) : Decidable (L.covers q) := by
  unfold Line.covers; infer_instance

/-- A square is attacked by a configuration `S` (a finite list of pieces) if some
piece covers it. -/
def attacked (S : List Line) (q : Square) : Prop := ∃ L ∈ S, L.covers q

instance (S : List Line) (q : Square) : Decidable (attacked S q) := by
  unfold attacked; infer_instance

/-- A square is safe if no piece of the configuration attacks it. -/
def safe (S : List Line) (q : Square) : Prop := ¬ attacked S q

/-! ## The king's `3 × 3` neighbourhood -/

/-- The nine offsets of a king's `3 × 3` neighbourhood (itself plus its eight
moves): all `(i, j)` with `i, j ∈ {-1, 0, 1}`. -/
def blockOffsets : Finset Square :=
  ({-1, 0, 1} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ)

/-- The eight king moves: the block offsets other than staying put. -/
def kingMoves : Finset Square := blockOffsets.erase (0, 0)



/-- The offsets a single line covers, relative to a center `p`. -/
def Line.blockCovered (L : Line) (p : Square) : Finset Square :=
  blockOffsets.filter (fun d => L.covers (p.1 + d.1, p.2 + d.2))

/-- The offsets covered by a whole configuration, relative to a center `p`. -/
def blockCovered (S : List Line) (p : Square) : Finset Square :=
  blockOffsets.filter (fun d => attacked S (p.1 + d.1, p.2 + d.2))

/-! ## Step 1: a line is functional in one coordinate -/



/-! ## Step 2: one line covers at most 3 of the 9 neighbourhood squares -/


/-! ## Step 3: `n` lines cover at most `3 * n` neighbourhood squares -/




/-! ## Step 4: fewer than three pieces cannot checkmate -/

/-- The king at `p` is **checkmated** by `S`: it is in check, and every one of its
eight moves lands on an attacked square. -/
def Checkmated (S : List Line) (p : Square) : Prop :=
  attacked S p ∧ ∀ d ∈ kingMoves, attacked S (p.1 + d.1, p.2 + d.2)



/-! ## Step 5: three pieces suffice — the threshold is sharp -/

/-- The horizontal line (rook) occupying the entire row `y = r`. -/
def rookRow (r : ℤ) : Line := ⟨0, 1, r, Or.inr one_ne_zero⟩



/-! ## Step 6: global escape — the board is never fully covered -/






end HilbertChess


