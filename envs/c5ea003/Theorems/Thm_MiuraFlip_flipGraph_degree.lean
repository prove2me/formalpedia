-- Prove2me | Theorems.Thm_MiuraFlip_flipGraph_degree
-- name    : MiuraFlip.flipGraph_degree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:58:40.785399+00:00
-- url     : https://prove2.me/theorems/12df1b78-7644-4b79-aa94-4541d491490e
-- title:
--   FlipGraph degree
-- statement:
--   Formal statement of `MiuraFlip.flipGraph_degree` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem MiuraFlip.flipGraph_degree(f : α → Bool) :
--       (flipGraph α).degree f = Fintype.card α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/MiuraFlipGraph/FlipGraph.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/MiuraFlipGraph/FlipGraph.lean#L90

-- Thm stub generated from Applications/MiuraFlipGraph/FlipGraph.lean
import Mathlib
import Definitions.Def_Applications_MiuraFlipGraph_FlipGraph
/-
Copyright (c) 2026. All rights reserved.

# The single-site flip graph of mountain–valley assignments

## Overview

This file builds the genuine *flip graph* (single-site recolouring graph, in the
sense of `Cereceda2009mixing`) of the mountain–valley (MV) assignments of an
origami crease pattern.  An MV assignment is a function `α → Bool` (mountain vs.
valley) on the set `α` of creases / sites; two assignments are joined by an edge
of the flip graph iff they differ at **exactly one** site (a single flip — the
elementary move of Glauber dynamics).

For the `m × n` Miura-ori we instantiate `α = MiuraFlip.V m n`, the
`(m+1) × (n+1)` lattice of crease vertices from `Basic.lean`.

## Main results

* `flipGraph_degree` — the flip graph is **regular**: every assignment has
  exactly `Fintype.card α` neighbours (one per site).
* `flipGraph_connected` — the flip graph is **connected** (any MV assignment can
  be reached from any other by single flips), so single-site Glauber dynamics is
  irreducible.
* `miura_flipGraph_degree` — corollary for the Miura-ori: the flip graph is
  `(m+1)(n+1)`-regular.

## Catalog connections

`Cereceda2009mixing` studies mixing of the single-site recolouring Markov chain;
its state graph is exactly this flip graph.  Regularity and connectivity are the
two structural prerequisites for that analysis.  The degree count reuses the
crease-vertex type `MiuraFlip.V` introduced in `Basic.lean`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): the single-site flip graph of MV assignments on a
finite site set α is isomorphic to the Boolean hypercube on α; in particular it
is |α|-regular and connected.  Bold corollary: for the Miura-ori it is
exactly (m+1)(n+1)-regular, matching the number of crease vertices.

EXPERIMENT (Experimenter): defined `flipGraph` with adjacency "differ at exactly
one site".  Degree computed by exhibiting the bijection x ↦ update f x (!f x)
between sites and neighbours.  Connectivity by induction on the (finite) set of
disagreeing sites: flip one disagreement at a time.

ANALYSIS (Analyst): regularity is the clean half; connectivity needs an
induction on the symmetric-difference size.  The graph is precisely the
hypercube Q_{|α|}; this identifies "flip graph of the Miura-ori" with a concrete
classical object and explains why Glauber dynamics is irreducible here.

CRITIQUE (Critic): the adjacency `∃! x, f x ≠ g x` is the faithful single-flip
relation (NOT a renamed hypercube); loopless and symm are real obligations.
Degree is a genuine `SimpleGraph.degree` value, established via an injective
image, not `decide`.

SYNTHESIS (PI): the Miura flip graph is (m+1)(n+1)-regular and connected — the
ergodicity backbone for the mixing questions of FUTURE_DIRECTIONS.md.
-/

open Finset

open MiuraFlip

variable {α : Type*} [Fintype α] [DecidableEq α]




/-
**Regularity.** Every MV assignment has exactly `Fintype.card α` neighbours
in the single-site flip graph — one flip per site.
-/

theorem MiuraFlip.flipGraph_degree(f : α → Bool) :
    (flipGraph α).degree f = Fintype.card α := by sorry
