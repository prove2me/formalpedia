-- Prove2me | Theorems.Thm_VertexSplitting_hasUnitIntervalRep_starSplitGraph
-- name    : VertexSplitting.hasUnitIntervalRep_starSplitGraph
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:28:53.524804+00:00
-- url     : https://prove2.me/theorems/c282466e-643c-4ecb-9e80-404aa05eba6a
-- title:
--   The pairing construction is a unit interval graph: place the centre copy `j` at `4j + 1` and
-- statement:
--   The pairing construction is a unit interval graph: place the centre copy `j` at `4j + 1` and
--   its (at most two) leaves `2j` and `2j + 1` at `4j` and `4j + 2`.
--
--   ```lean
--   theorem VertexSplitting.hasUnitIntervalRep_starSplitGraph(n m : ℕ) :
--       HasUnitIntervalRep (starSplitGraph n m) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/VertexSplittingExact.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/VertexSplittingExact.lean#L420

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

theorem VertexSplitting.hasUnitIntervalRep_starSplitGraph(n m : ℕ) :
    HasUnitIntervalRep (starSplitGraph n m) := by sorry
