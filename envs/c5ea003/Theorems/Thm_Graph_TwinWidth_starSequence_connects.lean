-- Prove2me | Theorems.Thm_Graph_TwinWidth_starSequence_connects
-- name    : Graph.TwinWidth.starSequence_connects
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:30.201723+00:00
-- url     : https://prove2.me/theorems/e5a390b9-679a-4960-91a7-1f3d85fe91fc
-- title:
--   The star sequence identifies all vertices of `l`: any two elements of `l` are
-- statement:
--   The star sequence identifies all vertices of `l`: any two elements of `l` are
--   related by the reflexive–transitive closure of the merge relation.
--
--   ```lean
--   theorem Graph.TwinWidth.starSequence_connects{l : List V} {a b : V} (ha : a ∈ l) (hb : b ∈ l) :
--       Relation.ReflTransGen (MergeRel (starSequence l)) a b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Contractions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Contractions.lean#L106

-- Thm stub generated from Geometry/Contractions.lean
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

theorem Graph.TwinWidth.starSequence_connects{l : List V} {a b : V} (ha : a ∈ l) (hb : b ∈ l) :
    Relation.ReflTransGen (MergeRel (starSequence l)) a b := by sorry
