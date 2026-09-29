-- Prove2me | solution 1 for VertexSplitting.isSplit_starSplitGraph
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:56:49.965529+00:00
-- url     : https://prove2.me/submissions/bf43dd0c-da96-40a3-aa4d-49e1e04b77ae

-- Sol generated from Bridges/VertexSplittingExact.lean
import Mathlib
import Definitions.Def_Bridges_VertexSplitting
import Definitions.Def_Bridges_VertexSplittingExact
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Exact splitting numbers for the smallest obstructions

This file complements `Bridges.VertexSplitting`, where the general theory of the vertex
splitting operation of *Hardness of Vertex Splitting: Cographs, Chordal Graphs, and Beyond*
is developed, with **exact** values of the splitting number for the smallest obstructions of
each of the three target classes studied there.

Main results:

* `isChordal_of_unitIntervalRep`: unit interval graphs are chordal (so the unit-interval
  splitting number always dominates the chordal one).
* `cograph_split_pathP4_exact`: the cograph splitting number of `P₄` is exactly one, and the
  single split can be taken exclusive.
* `chordal_split_cycleC4_exact`: the chordal splitting number of `C₄` is exactly one.
* `unitInterval_split_starK13_exact`: the unit-interval splitting number of the claw `K_{1,3}`
  is exactly one.
* `unitInterval_split_starK14_exact`: the unit-interval splitting number of `K_{1,4}` is also
  exactly one.  In particular the guess that `K_{1,n}` needs `n - 2` splits is false already
  for `n = 4`: pairing the leaves shows `⌈n/2⌉ - 1` splits suffice.
* `card_ge_of_split_clawFree_star` and `unitInterval_split_star_exact`: for every `n ≥ 1` the
  unit-interval splitting number of the star `K_{1,n}` is exactly `⌈n/2⌉ - 1`, by an exclusive
  splitting into `⌈n/2⌉` disjoint short paths, and a matching counting lower bound valid for
  every claw-free target.
-/

open VertexSplitting

open SimpleGraph

/-! ## Unit interval graphs are chordal -/


/-! ## `P₄`: one split makes a cograph -/








/-! ## `C₄`: one split makes a chordal graph -/









/-! ## Stars: one split makes `K_{1,3}` and `K_{1,4}` unit interval graphs -/


















/-! ## A general lower bound for stars

The claw `K_{1,3}` is the smallest obstruction to being a unit interval graph, and a star
`K_{1,n}` contains many of them.  Since claw-free graphs let every copy of the centre keep at
most two leaves, at least `⌈n/2⌉` copies of the centre are needed.
-/



theorem starGraph_adj_zero {n : ℕ} {v : Fin (n + 1)} (hv : v ≠ 0) :
    (starGraph n).Adj 0 v := by
  rw [starGraph, SimpleGraph.fromRel_adj]
  exact ⟨Ne.symm hv, Or.inl ⟨rfl, hv⟩⟩



/-! ### The matching upper bound for stars

Pairing up the leaves gives a splitting of `K_{1,n}` into `⌈n/2⌉` disjoint paths (`P₃`s, and one
`P₂` if `n` is odd), which is a unit interval graph.  Together with
`card_ge_of_split_clawFree_star` this determines the unit-interval splitting number of every
star exactly.
-/



theorem starGraph_adj_iff {n : ℕ} {u v : Fin (n + 1)} :
    (starGraph n).Adj u v ↔ (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0) := by
  rw [starGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨by simp [h1, Ne.symm h2], Or.inl ⟨h1, h2⟩⟩
    · exact ⟨by simp [h1]; exact h2, Or.inr ⟨h1, h2⟩⟩






open VertexSplitting in
theorem solution{n m : ℕ} (hm : 0 < m) (hcov : ∀ i : Fin n, (i : ℕ) / 2 < m) :
    IsSplit (starGraph n) (starSplitGraph n m) (starSplitMap n m) where
  surj := by
    intro v
    rcases Fin.eq_zero_or_eq_succ v with rfl | ⟨i, rfl⟩
    · exact ⟨Sum.inr ⟨0, hm⟩, rfl⟩
    · exact ⟨Sum.inl i, rfl⟩
  fiber_indep := by
    rintro (i | j) (i' | j') hxy hadj <;>
      simp only [starSplitMap, Sum.elim_inl, Sum.elim_inr] at hxy
    · simp [starSplitGraph, SimpleGraph.fromRel_adj] at hadj
    · exact Fin.succ_ne_zero i hxy
    · exact Fin.succ_ne_zero i' hxy.symm
    · simp [starSplitGraph, SimpleGraph.fromRel_adj] at hadj
  adj_proj := by
    rintro (i | j) (i' | j') hadj <;>
      simp only [starSplitGraph, SimpleGraph.fromRel_adj, or_false,
        false_or, and_false] at hadj <;>
      simp only [starSplitMap, Sum.elim_inl, Sum.elim_inr] <;>
      [skip; skip] <;>
      first
        | exact (starGraph_adj_zero (Fin.succ_ne_zero i)).symm
        | exact starGraph_adj_zero (Fin.succ_ne_zero i')
  cover := by
    intro u v huv
    rcases starGraph_adj_iff.mp huv with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
    · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hv
      refine ⟨Sum.inr ⟨(i : ℕ) / 2, hcov i⟩, Sum.inl i, rfl, rfl, ?_⟩
      simp [starSplitGraph, SimpleGraph.fromRel_adj]
    · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hu
      refine ⟨Sum.inl i, Sum.inr ⟨(i : ℕ) / 2, hcov i⟩, rfl, rfl, ?_⟩
      simp [starSplitGraph, SimpleGraph.fromRel_adj]
