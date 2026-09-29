-- Prove2me | Theorems.Thm_InfinitePachner_move_preserves_isTri
-- name    : InfinitePachner.move_preserves_isTri
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:29:55.684754+00:00
-- url     : https://prove2.me/theorems/9a6b4138-15d6-4875-879e-fdf7ac710579
-- title:
--   A bistellar move sends a triangulation to a triangulation.
-- statement:
--   A bistellar move sends a triangulation to a triangulation.
--
--   ```lean
--   theorem InfinitePachner.move_preserves_isTri{S T : Set ℝ} (hS : IsTri S) (h : Move S T) :
--       IsTri T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/InfinitePachner.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/InfinitePachner.lean#L87

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

theorem InfinitePachner.move_preserves_isTri{S T : Set ℝ} (hS : IsTri S) (h : Move S T) :
    IsTri T := by sorry
