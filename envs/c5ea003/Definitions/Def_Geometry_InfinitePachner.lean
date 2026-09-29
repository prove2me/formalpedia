-- Prove2me | Definitions.Def_Geometry_InfinitePachner
-- name    : Geometry_InfinitePachner
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:07.116066+00:00
-- url     : https://prove2.me/theorems/077f11c6-eef1-4a28-8031-dd78c6f2643a
-- title:
--   Aether Catalog definitions — Geometry_InfinitePachner
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.InfinitePachner`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/InfinitePachner.lean by skeleton subtraction
import Mathlib
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

namespace InfinitePachner

/-! ## Triangulations of the line and bistellar moves -/

/-- A locally finite triangulation of the real line, encoded by its vertex set:
it meets every bounded interval in a finite set and is unbounded in both
directions. -/
def IsTri (V : Set ℝ) : Prop :=
  (∀ a b : ℝ, (V ∩ Set.Icc a b).Finite) ∧
  (∀ x : ℝ, ∃ y ∈ V, x < y) ∧
  (∀ x : ℝ, ∃ y ∈ V, y < x)

/-- The `0`-move (subdivision): insert a new vertex. -/
def Subdiv (S T : Set ℝ) : Prop := ∃ x, x ∉ S ∧ T = insert x S

/-- The `1`-move (weld): delete an existing vertex. -/
def Weld (S T : Set ℝ) : Prop := ∃ x, x ∈ S ∧ T = S \ {x}

/-- A bistellar (Pachner) move: a subdivision or a weld. -/
def Move (S T : Set ℝ) : Prop := Subdiv S T ∨ Weld S T

/-- Pachner-equivalence: the reflexive–transitive closure of the move relation. -/
def Pachner (S T : Set ℝ) : Prop := Relation.ReflTransGen Move S T

/-! ## Reversibility and symmetry -/



/-! ## Moves preserve triangulations -/


/-! ## Pachner-equivalence is an equivalence relation -/





/-! ## Local finiteness of symmetric differences -/


/-! ## Finite Pachner theorem -/



/-! ## Infinite Pachner theorem -/

/-- The `n`-th milestone triangulation: agrees with `T` on the open window
`(-n, n)` and with `S` outside it.  At `n = 0` the window is empty, so
`milestone S T 0 = S`. -/
noncomputable def milestone (S T : Set ℝ) (n : ℕ) : Set ℝ :=
  (S \ Set.Ioo (-(n : ℝ)) n) ∪ (T ∩ Set.Ioo (-(n : ℝ)) n)







end InfinitePachner


