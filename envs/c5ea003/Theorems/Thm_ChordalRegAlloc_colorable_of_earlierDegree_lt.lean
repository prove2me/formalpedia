-- Prove2me | Theorems.Thm_ChordalRegAlloc_colorable_of_earlierDegree_lt
-- name    : ChordalRegAlloc.colorable_of_earlierDegree_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:39:27.715982+00:00
-- url     : https://prove2.me/theorems/b772c81d-831a-4917-8c3e-d91bae9a5960
-- title:
--   Colorable of earlierDegree lt
-- statement:
--   Formal statement of `ChordalRegAlloc.colorable_of_earlierDegree_lt` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ChordalRegAlloc.colorable_of_earlierDegree_lt(G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
--       (k : ℕ) (hk : ∀ v, (earlierNeighbours G v).card < k) : G.Colorable k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ChordalRegisterAllocation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ChordalRegisterAllocation.lean#L79

-- Thm stub generated from Bridges/ChordalRegisterAllocation.lean
import Mathlib
import Definitions.Def_Bridges_ChordalRegisterAllocation
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

open ChordalRegAlloc

variable {n : ℕ}




/-
**Greedy colouring lemma.**  If every vertex has strictly fewer than `k` earlier
neighbours, then `G` is `k`-colourable.  Processing vertices from largest to smallest, when a
vertex is coloured its already-coloured neighbours are exactly its earlier neighbours, of
which there are `< k`, so a free colour remains.  (No chordality is required for this bound.)
-/

theorem ChordalRegAlloc.colorable_of_earlierDegree_lt(G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hk : ∀ v, (earlierNeighbours G v).card < k) : G.Colorable k := by sorry
