-- Prove2me | Theorems.Thm_Graph_TwinWidth_starSequence_pairs_ne
-- name    : Graph.TwinWidth.starSequence_pairs_ne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:43.210014+00:00
-- url     : https://prove2.me/theorems/9414a3d8-55d2-47ab-b7f6-6dfd978f4fca
-- title:
--   Every operation in the star sequence merges two genuinely distinct vertices,
-- statement:
--   Every operation in the star sequence merges two genuinely distinct vertices,
--   provided the underlying list is non-circular (has no duplicates).
--
--   ```lean
--   theorem Graph.TwinWidth.starSequence_pairs_ne{l : List V} (h : l.Nodup) :
--       ∀ e ∈ starSequence l, e.1 ≠ e.2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Contractions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Contractions.lean#L57

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

theorem Graph.TwinWidth.starSequence_pairs_ne{l : List V} (h : l.Nodup) :
    ∀ e ∈ starSequence l, e.1 ≠ e.2 := by sorry
