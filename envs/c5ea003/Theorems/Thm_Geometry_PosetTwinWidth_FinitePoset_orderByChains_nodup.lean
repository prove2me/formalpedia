-- Prove2me | Theorems.Thm_Geometry_PosetTwinWidth_FinitePoset_orderByChains_nodup
-- name    : Geometry.PosetTwinWidth.FinitePoset.orderByChains_nodup
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:11:00.486983+00:00
-- url     : https://prove2.me/theorems/c0a08e2c-fc72-4845-baed-4490c7461dd7
-- title:
--   OrderByChains nodup
-- statement:
--   Formal statement of `Geometry.PosetTwinWidth.FinitePoset.orderByChains_nodup` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Geometry.PosetTwinWidth.FinitePoset.orderByChains_nodup{k : ℕ} (C : P.ChainCover k) :
--       (P.orderByChains C).Nodup := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PosetTwinWidth/LinearBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PosetTwinWidth/LinearBound.lean#L169

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

theorem Geometry.PosetTwinWidth.FinitePoset.orderByChains_nodup{k : ℕ} (C : P.ChainCover k) :
    (P.orderByChains C).Nodup := by sorry
