-- Prove2me | Theorems.Thm_InfinitePachner_symmDiff_card_move
-- name    : InfinitePachner.symmDiff_card_move
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:30:03.167302+00:00
-- url     : https://prove2.me/theorems/11253edb-40f3-4640-a0a0-1c4a30144225
-- title:
--   Auxiliary induction: if the symmetric difference of `S` and `T` is finite
-- statement:
--   Auxiliary induction: if the symmetric difference of `S` and `T` is finite
--   with `n` elements, then `S` and `T` are joined by a finite sequence of moves.
--
--   ```lean
--   theorem InfinitePachner.symmDiff_card_move:
--       ∀ (n : ℕ) (S T : Set ℝ), ((S \ T) ∪ (T \ S)).Finite →
--         ((S \ T) ∪ (T \ S)).ncard = n → Pachner S T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/InfinitePachner.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/InfinitePachner.lean#L158

-- Thm stub generated from Geometry/InfinitePachner.lean
import Mathlib
import Definitions.Def_Geometry_InfinitePachner
/-
# An Infinite Pachner Theorem for Locally Finite Triangulations of the Line

Pachner's theorem states that any two triangulations of a piecewise-linear
manifold are related by a finite sequence of *bistellar moves* (Pachner moves).
Its *infinite* analogue asks: if `S` and `T` are two **locally finite**
triangulations of a manifold `M`, are they related by a *locally finite*
sequence of bistellar moves?

This file develops the one–dimensional case (`M = ℝ`) completely and rigorously.
A locally finite triangulation of the real line is encoded by its vertex set
`V ⊆ ℝ`: a set that meets every bounded interval in a finite set and is
unbounded above and below.  In dimension one there are exactly two Pachner
moves:

* the `0`-move (**subdivision**): insert a new vertex into an edge;
* the `1`-move (**weld**): delete a vertex, merging its two incident edges.

We build a chain of results culminating in the *infinite Pachner theorem* for
the line.

## Main results

* `subdiv_iff_weld`      — every subdivision is the inverse of a weld (reversibility).
* `move_symm`            — the bistellar-move relation is symmetric.
* `move_preserves_isTri` — a bistellar move sends a triangulation to a triangulation.
* `pachner_equivalence`  — Pachner-equivalence is an equivalence relation.
* `symmDiff_finite_move` — **finite Pachner**: vertex sets with finite symmetric
                           difference are joined by a finite sequence of moves.
* `infinite_pachner`     — **infinite Pachner (dimension 1)**: any two locally
                           finite triangulations of `ℝ` are joined by a locally
                           finite (window-stabilizing) sequence of finite blocks
                           of bistellar moves.

## References

* U. Pachner, *P.L. homeomorphic manifolds are equivalent by elementary
  shellings*, European J. Combin. 12 (1991).
-/


open Set

open InfinitePachner

/-! ## Triangulations of the line and bistellar moves -/






/-! ## Reversibility and symmetry -/



/-! ## Moves preserve triangulations -/


/-! ## Pachner-equivalence is an equivalence relation -/





/-! ## Local finiteness of symmetric differences -/


/-! ## Finite Pachner theorem -/

theorem InfinitePachner.symmDiff_card_move:
    ∀ (n : ℕ) (S T : Set ℝ), ((S \ T) ∪ (T \ S)).Finite →
      ((S \ T) ∪ (T \ S)).ncard = n → Pachner S T := by sorry
