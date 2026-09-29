-- Prove2me | solution 1 for InfinitePachner.milestone_symmDiff_finite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:12.384714+00:00
-- url     : https://prove2.me/submissions/31fada4b-3493-44a8-8430-cd1ce758d1a8

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


/-- Membership characterization of a milestone. -/
theorem mem_milestone (S T : Set ℝ) (k : ℕ) (y : ℝ) :
    y ∈ milestone S T k ↔
      (y ∈ S ∧ y ∉ Set.Ioo (-(k:ℝ)) k) ∨ (y ∈ T ∧ y ∈ Set.Ioo (-(k:ℝ)) k) := by
  simp only [milestone, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]

/-- Every milestone is contained in the union of the two vertex sets. -/
theorem milestone_subset_union (S T : Set ℝ) (k : ℕ) : milestone S T k ⊆ S ∪ T := by
  intro y hy; rw [mem_milestone] at hy
  rcases hy with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h






open InfinitePachner in
theorem solution{S T : Set ℝ}
    (hS : ∀ a b : ℝ, (S ∩ Set.Icc a b).Finite)
    (hT : ∀ a b : ℝ, (T ∩ Set.Icc a b).Finite) (n : ℕ) :
    ((milestone S T n \ milestone S T (n + 1)) ∪
      (milestone S T (n + 1) \ milestone S T n)).Finite := by
  apply Set.Finite.subset ((hS (-((n:ℝ)+1)) ((n:ℝ)+1)).union (hT (-((n:ℝ)+1)) ((n:ℝ)+1)))
  have ecast : ((n+1:ℕ):ℝ) = (n:ℝ)+1 := by push_cast; ring
  have hwinsub : Set.Ioo (-(n:ℝ)) (n:ℝ) ⊆ Set.Ioo (-((n:ℝ)+1)) ((n:ℝ)+1) := by
    apply Set.Ioo_subset_Ioo <;> linarith [Nat.cast_nonneg (α := ℝ) n]
  intro y hy
  have hST : y ∈ S ∨ y ∈ T := by
    rcases hy with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact milestone_subset_union S T _ h1
  have hwin : y ∈ Set.Ioo (-((n:ℝ)+1)) ((n:ℝ)+1) := by
    by_contra hno
    have houtn : y ∉ Set.Ioo (-(n:ℝ)) (n:ℝ) := fun h => hno (hwinsub h)
    have hout1 : y ∉ Set.Ioo (-((n+1:ℕ):ℝ)) ((n+1:ℕ):ℝ) := by rw [ecast]; exact hno
    have hagree : y ∈ milestone S T n ↔ y ∈ milestone S T (n+1) := by
      rw [mem_milestone, mem_milestone]
      constructor
      · rintro (⟨hyS, _⟩ | ⟨_, hin⟩)
        · exact Or.inl ⟨hyS, hout1⟩
        · exact absurd hin houtn
      · rintro (⟨hyS, _⟩ | ⟨_, hin⟩)
        · exact Or.inl ⟨hyS, houtn⟩
        · exact absurd hin hout1
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hagree.1 h1)
    · exact h2 (hagree.2 h1)
  have hwin' : y ∈ Set.Icc (-((n:ℝ)+1)) ((n:ℝ)+1) := Set.Ioo_subset_Icc_self hwin
  rcases hST with h | h
  · exact Or.inl ⟨h, hwin'⟩
  · exact Or.inr ⟨h, hwin'⟩
