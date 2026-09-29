-- Prove2me | solution 1 for InfinitePachner.milestone_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:11.945466+00:00
-- url     : https://prove2.me/submissions/c561ceb1-6c0b-4dc9-8bc5-52120dfab157

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







open InfinitePachner in
theorem solution{S T : Set ℝ} (a b : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, milestone S T n ∩ Set.Icc a b = T ∩ Set.Icc a b := by
  refine ⟨⌈max |a| |b|⌉₊ + 1, ?_⟩
  intro n hn
  have key : max |a| |b| < (n:ℝ) := by
    have h1 : max |a| |b| ≤ (⌈max |a| |b|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈max |a| |b|⌉₊ + 1 : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    push_cast at h2; linarith
  have hb : b < n := lt_of_le_of_lt (le_trans (le_abs_self b) (le_max_right _ _)) key
  have ha : -(n:ℝ) < a := by
    have h3 : |a| < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) key
    have h4 : -|a| ≤ a := neg_abs_le a
    linarith
  ext y
  simp only [Set.mem_inter_iff, mem_milestone, Set.mem_Icc, Set.mem_Ioo]
  constructor
  · rintro ⟨hm, hy1, hy2⟩
    refine ⟨?_, hy1, hy2⟩
    rcases hm with ⟨_, hno⟩ | ⟨hT, _⟩
    · exact absurd ⟨by linarith, by linarith⟩ hno
    · exact hT
  · rintro ⟨hT, hy1, hy2⟩
    exact ⟨Or.inr ⟨hT, by constructor <;> linarith⟩, hy1, hy2⟩
