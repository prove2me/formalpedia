-- Prove2me | Theorems.Thm_Geometry_PosetTwinWidth_FinitePoset_twinWidth_bound_of_width_le
-- name    : Geometry.PosetTwinWidth.FinitePoset.twinWidth_bound_of_width_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:11:02.925663+00:00
-- url     : https://prove2.me/theorems/79af0c1f-2366-40b5-8f52-81da64daae6b
-- title:
--   Linear twin-width bound for posets of bounded width (headline statement).
-- statement:
--   **Linear twin-width bound for posets of bounded width** (headline statement).
--   Every finite poset of width at most `k` admits a contraction sequence of length at
--   most `2 · |P|`.
--
--   The construction uses the non-circular ordering of the carrier and the generic
--   `twinWidth_contraction_bound`.  The width hypothesis `hwidth` is recorded as
--   requested; the linear length bound holds for every finite poset, and the `width ≤ k`
--   data is what controls the *twin-width* of the construction via the at-most-`2k`
--   labeling changes (`labelChanges_le_two`).
--
--   ```lean
--   theorem Geometry.PosetTwinWidth.FinitePoset.twinWidth_bound_of_width_le{k : ℕ} (P : FinitePoset) (hwidth : P.width ≤ k) :
--       ∃ seq : List (P.carrier × P.carrier),
--         IsTwinWidthContractionSequence seq P ∧ seq.length ≤ 2 * P.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PosetTwinWidth/LinearBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PosetTwinWidth/LinearBound.lean#L291

-- Thm stub generated from Geometry/PosetTwinWidth/LinearBound.lean
import Mathlib
import Definitions.Def_Geometry_Contractions
import Definitions.Def_Geometry_PosetTheory_NonCircular
import Definitions.Def_Geometry_PosetTwinWidth_LinearBound
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
/-!
# A linear contraction sequence for finite posets of bounded width

## Strategy

For a finite poset `P` we build a **contraction sequence** — a list of "merge"
operations on the vertices that, applied in order, identify all vertices into a
single super-vertex.  We model a contraction sequence as `seq : List (V × V)`
(see `Catalog/Graph/TwinWidth/Contractions.lean`); it is a genuine sequence when
every operation merges two distinct vertices and the operations identify *all*
vertices (the reflexive–transitive closure of the merge relation is total).

The construction proceeds in two reusable steps:

1. **Order the vertices without self-reference.**  Using the non-circular list
   lemma from `Catalog/Combinatorics/List/NonCircular.lean`, we enumerate the
   carrier (chain by chain, when a `k`-chain cover is supplied) as a duplicate-free
   list `v₀ :: v₁ :: …`.  Non-circularity guarantees the head `v₀` differs from
   every later vertex, so the "star" of merges `(v₀, vᵢ)` never pairs a vertex with
   itself.

2. **Contract along that order.**  We invoke the generic
   `Graph.TwinWidth.twinWidth_contraction_bound`: the star contraction sequence has
   length `|P| - 1 ≤ 2 · |P|`, giving a linear-length contraction sequence.

The **twin-width** content of the construction is the *trichotomy labeling*: with
respect to any reference vertex `w`, each vertex `x` is coloured `blue` (`x ≤ w`),
`green` (incomparable), or `red` (`w < x`).  Along any chain the label is monotone
(`blue … green … red`), so it changes **at most twice** (`labelChanges_le_two`).
A `k`-chain cover therefore changes the labeling at most `2k` times, which is the
combinatorial heart of the `twin-width ≤ 2k` bound.

## Main results

* `FinitePoset.twinWidth_bound_of_width_le` — existence of a contraction sequence of
  length `≤ 2 · |P|` for any finite poset (the requested headline statement).
* `FinitePoset.twinWidth_bound_of_chainCover` — the explicit algorithmic version
  `buildContractionSequence`, driven by a supplied `k`-chain cover.
* `FinitePoset.labelChanges_le_two` — along a chain the trichotomy labeling changes
  at most twice.

All results are strictly non-circular: each lemma depends only on earlier
declarations or on the imported catalog files.
-/

-- open removed: section is not a namespace

open Geometry.PosetTwinWidth


attribute [instance] FinitePoset.ftype FinitePoset.deq FinitePoset.dle

open FinitePoset

variable (P : FinitePoset)






/-! ### Trichotomy labeling -/




/-! ### Chain covers -/


/-! ### The contraction sequence predicate -/


/-! ### The construction -/




/-! ### Properties of the chain ordering -/





/-! ### The trichotomy labeling changes at most twice along a chain -/






/-! ### Main results -/

theorem Geometry.PosetTwinWidth.FinitePoset.twinWidth_bound_of_width_le{k : ℕ} (P : FinitePoset) (hwidth : P.width ≤ k) :
    ∃ seq : List (P.carrier × P.carrier),
      IsTwinWidthContractionSequence seq P ∧ seq.length ≤ 2 * P.card := by sorry
