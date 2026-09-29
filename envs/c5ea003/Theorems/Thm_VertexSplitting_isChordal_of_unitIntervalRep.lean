-- Prove2me | Theorems.Thm_VertexSplitting_isChordal_of_unitIntervalRep
-- name    : VertexSplitting.isChordal_of_unitIntervalRep
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:28:42.601198+00:00
-- url     : https://prove2.me/theorems/8ee6d2a4-4946-48fb-9dfb-916d0931ce17
-- title:
--   Unit interval graphs are chordal.
-- statement:
--   **Unit interval graphs are chordal.**  Along an induced cycle of length at least four,
--   consider a vertex `c i` whose point `p (c i)` is leftmost.  Its two cycle neighbours lie in
--   `[p (c i), p (c i) + 1]`, hence within distance one of each other, hence adjacent — contradicting
--   that the cycle is induced.
--
--   ```lean
--   theorem VertexSplitting.isChordal_of_unitIntervalRep{W : Type*} {H : SimpleGraph W}
--       (h : HasUnitIntervalRep H) : IsChordal H := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/VertexSplittingExact.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/VertexSplittingExact.lean#L37

-- Thm stub generated from Bridges/VertexSplittingExact.lean
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

theorem VertexSplitting.isChordal_of_unitIntervalRep{W : Type*} {H : SimpleGraph W}
    (h : HasUnitIntervalRep H) : IsChordal H := by sorry
