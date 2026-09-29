-- Prove2me | solution 1 for VertexSplitting.hasUnitIntervalRep_starSplitGraph
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:56:47.421602+00:00
-- url     : https://prove2.me/submissions/9637f342-c412-4d40-adc0-aedee2337f72

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






/-! ### The matching upper bound for stars

Pairing up the leaves gives a splitting of `K_{1,n}` into `⌈n/2⌉` disjoint paths (`P₃`s, and one
`P₂` if `n` is odd), which is a unit interval graph.  Together with
`card_ge_of_split_clawFree_star` this determines the unit-interval splitting number of every
star exactly.
-/









open VertexSplitting in
theorem solution(n m : ℕ) :
    HasUnitIntervalRep (starSplitGraph n m) := by
  have key : ∀ a b : ℤ, |(a : ℝ) - (b : ℝ)| ≤ 1 ↔ |a - b| ≤ 1 := by
    intro a b
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Iff.rfl
  refine ⟨fun x => ((Sum.elim (fun i : Fin n => 2 * (i : ℕ))
      (fun j : Fin m => 4 * (j : ℕ) + 1) x : ℤ) : ℝ), ?_⟩
  rintro (i | j) (i' | j') <;>
    simp only [starSplitGraph, SimpleGraph.fromRel_adj, Sum.elim_inl, Sum.elim_inr, reduceCtorEq,
      or_false, false_or, and_false, ne_eq, Sum.inl.injEq, Sum.inr.injEq,
      Fin.ext_iff, key, abs_le, not_false_eq_true, true_and, false_iff, not_and] <;>
    omega
