-- Prove2me | solution 1 for InfinitePachner.symmDiff_card_move
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:13.306755+00:00
-- url     : https://prove2.me/submissions/fc02cc0c-3ef9-45bd-b951-14cdba753a3d

-- Sol generated from Geometry/InfinitePachner.lean
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



/-! ## Infinite Pachner theorem -/









open InfinitePachner in
theorem solution:
    ∀ (n : ℕ) (S T : Set ℝ), ((S \ T) ∪ (T \ S)).Finite →
      ((S \ T) ∪ (T \ S)).ncard = n → Pachner S T := by
  intro n
  induction n with
  | zero =>
    intro S T hfin hcard
    have hempty : (S \ T) ∪ (T \ S) = ∅ := (Set.ncard_eq_zero hfin).1 hcard
    have hST : S = T := by
      rw [Set.union_empty_iff, Set.diff_eq_empty, Set.diff_eq_empty] at hempty
      exact Set.Subset.antisymm hempty.1 hempty.2
    rw [hST]; exact Relation.ReflTransGen.refl
  | succ m ih =>
    intro S T hfin hcard
    have hne : ((S \ T) ∪ (T \ S)).Nonempty := by
      rw [← Set.ncard_pos hfin, hcard]; omega
    obtain ⟨x, hx⟩ := hne
    rcases hx with hx | hx
    · refine Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (Or.inr ⟨x, hx.1, rfl⟩ : Move S (S \ {x}))) ?_
      have hDeq : ((S \ {x}) \ T) ∪ (T \ (S \ {x})) = ((S \ T) ∪ (T \ S)) \ {x} := by
        ext y
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        by_cases hy : y = x <;> simp_all
      refine ih (S \ {x}) T (by rw [hDeq]; exact hfin.diff) ?_
      rw [hDeq, Set.ncard_diff_singleton_of_mem (Set.mem_union_left _ hx), hcard]
      omega
    · refine Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (Or.inl ⟨x, hx.2, rfl⟩ : Move S (insert x S))) ?_
      have hDeq : ((insert x S) \ T) ∪ (T \ (insert x S)) = ((S \ T) ∪ (T \ S)) \ {x} := by
        ext y
        simp only [Set.mem_union, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
        by_cases hy : y = x <;> simp_all
      refine ih (insert x S) T (by rw [hDeq]; exact hfin.diff) ?_
      rw [hDeq, Set.ncard_diff_singleton_of_mem (Set.mem_union_right _ hx), hcard]
      omega
