-- Prove2me | solution 1 for InfinitePachner.move_preserves_isTri
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:12.83122+00:00
-- url     : https://prove2.me/submissions/2ad4a883-55e8-43d4-848c-c120a78e938a

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
theorem solution{S T : Set ℝ} (hS : IsTri S) (h : Move S T) :
    IsTri T := by
  obtain ⟨hLF, hUp, hDn⟩ := hS
  rcases h with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro a b
      apply Set.Finite.subset ((hLF a b).insert x)
      intro y hy
      rcases hy with ⟨hyi, hyIcc⟩
      rcases hyi with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hyIcc⟩
    · intro z; obtain ⟨y, hy, hyz⟩ := hUp z; exact ⟨y, Or.inr hy, hyz⟩
    · intro z; obtain ⟨y, hy, hyz⟩ := hDn z; exact ⟨y, Or.inr hy, hyz⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro a b
      exact Set.Finite.subset (hLF a b) (fun y hy => ⟨hy.1.1, hy.2⟩)
    · intro z
      obtain ⟨y1, hy1, hy1z⟩ := hUp z
      obtain ⟨y2, hy2, hy12⟩ := hUp y1
      by_cases hxe : y2 = x
      · refine ⟨y1, ⟨hy1, ?_⟩, hy1z⟩
        intro hc; rw [Set.mem_singleton_iff] at hc
        rw [hc, ← hxe] at hy12; exact absurd hy12 (lt_irrefl _)
      · exact ⟨y2, ⟨hy2, by simp [hxe]⟩, lt_trans hy1z hy12⟩
    · intro z
      obtain ⟨y1, hy1, hy1z⟩ := hDn z
      obtain ⟨y2, hy2, hy12⟩ := hDn y1
      by_cases hxe : y2 = x
      · refine ⟨y1, ⟨hy1, ?_⟩, hy1z⟩
        intro hc; rw [Set.mem_singleton_iff] at hc
        rw [hc, ← hxe] at hy12; exact absurd hy12 (lt_irrefl _)
      · exact ⟨y2, ⟨hy2, by simp [hxe]⟩, lt_trans hy12 hy1z⟩
