-- Prove2me | Definitions.Def_Bridges_ChordalRegisterAllocation
-- name    : Bridges_ChordalRegisterAllocation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:15.440001+00:00
-- url     : https://prove2.me/theorems/9314a843-b0d2-4ac2-9174-75ddc64c0327
-- title:
--   Aether Catalog definitions — Bridges_ChordalRegisterAllocation
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ChordalRegisterAllocation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ChordalRegisterAllocation.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Register allocation for SSA programs: chordal interference graphs are perfect

Register allocation assigns program variables to a fixed bank of CPU registers.  Two
variables *interfere* when they are simultaneously live; a legal assignment gives interfering
variables distinct registers, i.e. a proper colouring of the **interference graph** `G`, using
`χ(G)` colours in the optimum.

For programs in **Static Single Assignment (SSA)** form the interference graph is *chordal*:
every cycle of length `≥ 4` has a chord.  Equivalently, `G` admits a **perfect elimination
ordering (PEO)** — an enumeration `v₁, …, vₙ` of the vertices such that, for each `vᵢ`, the
neighbours of `vᵢ` occurring *earlier* in the order form a clique.  This file proves the
central structural fact behind optimal SSA register allocation:

> **Chordal graphs are perfect.**  If `G` has a perfect elimination ordering then
> `χ(G) = ω(G)`: greedy colouring along the order uses exactly `ω(G) = ` (the maximum number
> of simultaneously live variables) registers, and no colouring can do better.

We work with the concrete elimination order given by the linear order on `Fin n`, so a PEO is
the hypothesis `IsPerfectElimOrder G : ∀ v, G.IsClique (earlierNeighbours G v)`.

## Main results

* `colorable_of_earlierDegree_lt` — the **greedy colouring lemma**: if every vertex has fewer
  than `k` earlier neighbours, then `G` is `k`-colourable (no chordality needed).
* `earlier_insert_isClique`, `earlierDegree_succ_le_cliqueNum` — under a PEO each vertex with
  its earlier neighbours is a clique, so `earlierDegree v + 1 ≤ ω(G)`.
* `colorable_cliqueNum_of_peo` — a PEO graph is `ω(G)`-colourable (linear-scan optimality).
* `chromaticNumber_eq_cliqueNum_of_peo` — **perfectness of chordal graphs**: `χ(G) = ω(G)`.

## Interval graphs as a special case

Interval / linear-scan interference graphs (variables with contiguous live ranges) are a
strict subclass of chordal graphs.  We recover them:

* `interferenceGraph_isPEO` — when live ranges are sorted by start point (`Monotone lo`), the
  interval interference graph has a perfect elimination ordering;
* `interval_chromaticNumber_eq_cliqueNum` — hence `χ = ω` for interval graphs, obtained here
  purely as a corollary of the general chordal theorem.

This strictly generalises the interval-graph analysis of register allocation to the full SSA
(chordal) setting: interval ⊊ chordal, and the optimal register count is the clique number in
both.
-/

open Finset SimpleGraph

namespace ChordalRegAlloc

variable {n : ℕ}

/-- The neighbours of `v` occurring *earlier* than `v` in the elimination order on `Fin n`. -/
def earlierNeighbours (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    Finset (Fin n) :=
  univ.filter (fun w => w < v ∧ G.Adj v w)


/-- `G` has a **perfect elimination ordering** (relative to the linear order on `Fin n`) when
the earlier neighbours of every vertex form a clique.  This is the order-theoretic
characterisation of chordality. -/
def IsPerfectElimOrder (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.IsClique (earlierNeighbours G v : Set (Fin n))

/-
**Greedy colouring lemma.**  If every vertex has strictly fewer than `k` earlier
neighbours, then `G` is `k`-colourable.  Processing vertices from largest to smallest, when a
vertex is coloured its already-coloured neighbours are exactly its earlier neighbours, of
which there are `< k`, so a free colour remains.  (No chordality is required for this bound.)
-/

/-
Under a PEO, a vertex together with its earlier neighbours forms a clique.
-/

/-
Under a PEO, `earlierDegree v + 1 ≤ ω(G)`: the earlier-neighbour count of every vertex is
bounded by the clique number.
-/

/-
**Linear-scan optimality for chordal graphs.**  A graph with a perfect elimination
ordering is colourable with `ω(G)` colours.
-/

/-
**Chordal graphs are perfect.**  If `G` has a perfect elimination ordering then its
chromatic number equals its clique number.  For register allocation this says: the optimal
number of registers for an SSA program equals the maximum number of simultaneously live
variables, and greedy colouring along the elimination order attains it.
-/

/-! ## Interval graphs as a special case of chordal graphs -/

/-- Two distinct variables *interfere* when their closed live ranges `[lo, hi]` overlap. -/
def Interfere (lo hi : Fin n → ℕ) (i j : Fin n) : Prop :=
  i ≠ j ∧ lo i ≤ hi j ∧ lo j ≤ hi i

lemma Interfere.symm {lo hi : Fin n → ℕ} {i j : Fin n} (h : Interfere lo hi i j) :
    Interfere lo hi j i := ⟨h.1.symm, h.2.2, h.2.1⟩

/-- The interval interference graph on `Fin n`. -/
def interferenceGraph (lo hi : Fin n → ℕ) : SimpleGraph (Fin n) where
  Adj i j := Interfere lo hi i j
  symm := fun _ _ h => h.symm
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (lo hi : Fin n → ℕ) : DecidableRel (interferenceGraph lo hi).Adj := by
  intro i j; unfold interferenceGraph Interfere; infer_instance


/-
**Interval graphs are chordal.**  When live ranges are enumerated in increasing order of
their start points (`Monotone lo`), the interval interference graph has a perfect elimination
ordering: the earlier neighbours of a variable are all live at its start point, hence pairwise
overlap.  (Well-formedness `lo ≤ hi` of the ranges is not even needed for chordality.)
-/



end ChordalRegAlloc


