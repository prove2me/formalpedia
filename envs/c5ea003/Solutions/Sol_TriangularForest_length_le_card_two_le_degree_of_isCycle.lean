-- Prove2me | solution 1 for TriangularForest.length_le_card_two_le_degree_of_isCycle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:42:56.381162+00:00
-- url     : https://prove2.me/submissions/e716e502-41b5-4027-8302-adec7a473ebf

-- Sol generated from Logic/TriangularForest/Defs.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs
import Theorems.Thm_TriangularForest_two_le_degree_of_mem_support

/-!
# Triangular forests

A *triangular forest* is a graph in which every 2-connected block is a single edge or a
triangle.  Equivalently (and this is the definition we use, since it is the most convenient
one to reason with) a graph is a triangular forest exactly when **every cycle has length 3**.

The two descriptions agree: a 2-connected graph on at least four vertices always contains a
cycle of length at least four, and two triangles sharing an edge span a 4-cycle, so "every
cycle is a triangle" forces every block to be an edge or a triangle, and conversely.

This file sets up the basic theory:

* `TriangularForest.IsTriangularForest` — the definition;
* closure under subgraphs (`IsTriangularForest.mono`) and induced subgraphs
  (`IsTriangularForest.induce`);
* forests are triangular forests;
* every vertex on a cycle has degree at least two, hence a cycle is no longer than the number
  of vertices of degree at least two (`IsCycle.length_le_card_two_le_degree`);
* consequently any graph with at most three vertices of degree ≥ 2 is a triangular forest
  (`isTriangularForest_of_card_two_le_degree_le_three`), which is the workhorse for verifying
  concrete examples.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G H : SimpleGraph V}







variable [Fintype V] [DecidableRel G.Adj]


variable [DecidableEq V]





open TriangularForest in
theorem solution{v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    c.length ≤ #{x ∈ (univ : Finset V) | 2 ≤ G.degree x} := by
  classical
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hlen : c.support.tail.length = c.length := by
    have := c.length_support
    simp [List.length_tail, this]
  have hsub : c.support.tail.toFinset ⊆ {x ∈ (univ : Finset V) | 2 ≤ G.degree x} := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    have : x ∈ c.support := List.mem_of_mem_tail hx
    simp [two_le_degree_of_mem_support hc this]
  calc c.length = c.support.tail.toFinset.card := by
        rw [List.toFinset_card_of_nodup hnodup, hlen]
    _ ≤ _ := Finset.card_le_card hsub
