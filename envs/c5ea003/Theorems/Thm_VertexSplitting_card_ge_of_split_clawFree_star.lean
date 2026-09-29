-- Prove2me | Theorems.Thm_VertexSplitting_card_ge_of_split_clawFree_star
-- name    : VertexSplitting.card_ge_of_split_clawFree_star
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:28:25.837885+00:00
-- url     : https://prove2.me/theorems/8e4b2642-c646-4ed5-af01-eadd136eaffc
-- title:
--   Lower bound for stars.
-- statement:
--   **Lower bound for stars.**  If a splitting of the star `K_{1,n}` produces a claw-free graph,
--   then the result has at least `n + ⌈n/2⌉` vertices: every copy of the centre can keep at most two
--   leaves, so at least `⌈n/2⌉` copies of the centre are needed, on top of the `n` leaves.
--
--   ```lean
--   theorem VertexSplitting.card_ge_of_split_clawFree_star{n : ℕ} {W : Type*} [Fintype W]
--       {H : SimpleGraph W} {f : W → Fin (n + 1)} (h : IsSplit (starGraph n) H f)
--       (hclaw : ¬ HasInducedClaw H) : n + (n + 1) / 2 ≤ Fintype.card W := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/VertexSplittingExact.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/VertexSplittingExact.lean#L269

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

theorem VertexSplitting.card_ge_of_split_clawFree_star{n : ℕ} {W : Type*} [Fintype W]
    {H : SimpleGraph W} {f : W → Fin (n + 1)} (h : IsSplit (starGraph n) H f)
    (hclaw : ¬ HasInducedClaw H) : n + (n + 1) / 2 ≤ Fintype.card W := by sorry
