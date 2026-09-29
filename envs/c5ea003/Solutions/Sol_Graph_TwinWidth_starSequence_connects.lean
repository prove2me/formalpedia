-- Prove2me | solution 1 for Graph.TwinWidth.starSequence_connects
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:26:18.319728+00:00
-- url     : https://prove2.me/submissions/e12958b7-3673-4431-92e9-ec3fbe51236d

-- Sol generated from Geometry/Contractions.lean
import Mathlib
import Definitions.Def_Geometry_Contractions
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Generic contraction sequences for twin-width

A *contraction sequence* of a graph repeatedly merges two vertices until a single
vertex remains.  We model a contraction sequence abstractly as a list of merge
operations `seq : List (V × V)`, where the operation `(a, b)` identifies the two
super-vertices currently containing `a` and `b`.

Two pieces of data make such a list a genuine contraction sequence:

* every operation merges two *distinct* vertices (no self-reference), and
* the operations identify *all* vertices into one final super-vertex, i.e. the
  reflexive–transitive closure of the merge relation is total on `V`.

This file develops the generic *star* contraction sequence built from a linear
ordering of the vertices, and proves the generic length bound
`twinWidth_contraction_bound`, which downstream files reuse instead of re-deriving.
-/

open Graph.TwinWidth

variable {V : Type*}










/-- Every vertex of `l` is `MergeRel`-related to the head (going *towards* the head). -/
theorem starSequence_cons {v₀ : V} {rest : List V} : starSequence (v₀ :: rest) = rest.map (fun v => (v₀, v)) := rfl
theorem starSequence_toHead {v₀ : V} {rest : List V} {a : V}
    (ha : a ∈ v₀ :: rest) :
    Relation.ReflTransGen (MergeRel (starSequence (v₀ :: rest))) a v₀ := by
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Relation.ReflTransGen.refl
  · refine Relation.ReflTransGen.single ?_
    right
    simp only [starSequence_cons, List.mem_map]
    exact ⟨a, ha, rfl⟩

/-- Every vertex of `l` is `MergeRel`-related from the head (going *from* the head). -/
theorem starSequence_fromHead {v₀ : V} {rest : List V} {a : V}
    (ha : a ∈ v₀ :: rest) :
    Relation.ReflTransGen (MergeRel (starSequence (v₀ :: rest))) v₀ a := by
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Relation.ReflTransGen.refl
  · refine Relation.ReflTransGen.single ?_
    left
    simp only [starSequence_cons, List.mem_map]
    exact ⟨a, ha, rfl⟩




open Graph.TwinWidth in
theorem solution{l : List V} {a b : V} (ha : a ∈ l) (hb : b ∈ l) :
    Relation.ReflTransGen (MergeRel (starSequence l)) a b := by
  cases l with
  | nil => simp at ha
  | cons v₀ rest =>
    exact (starSequence_toHead ha).trans (starSequence_fromHead hb)
