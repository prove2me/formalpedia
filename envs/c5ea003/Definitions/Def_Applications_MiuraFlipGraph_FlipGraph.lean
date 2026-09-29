-- Prove2me | Definitions.Def_Applications_MiuraFlipGraph_FlipGraph
-- name    : Applications_MiuraFlipGraph_FlipGraph
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:39.032512+00:00
-- url     : https://prove2.me/theorems/d7a7b8a0-08f5-4da5-87cf-c3dd3bcad5c8
-- title:
--   Aether Catalog definitions — Applications_MiuraFlipGraph_FlipGraph
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.MiuraFlipGraph.FlipGraph`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/MiuraFlipGraph/FlipGraph.lean by skeleton subtraction
import Mathlib
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

namespace MiuraFlip

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Lattice vertices of the `m × n` Miura crease pattern (same `V` as in
`Basic.lean`; inlined here to keep this file self-contained). -/
abbrev V (m n : ℕ) := Fin (m + 1) × Fin (n + 1)

/-- The single-site flip graph on MV assignments `α → Bool`: two assignments are
adjacent iff they differ at exactly one site. -/
def flipGraph (α : Type*) [DecidableEq α] : SimpleGraph (α → Bool) where
  Adj f g := ∃! x, f x ≠ g x
  symm := by
    intro f g h
    obtain ⟨x, hx, hu⟩ := h
    exact ⟨x, fun h => hx h.symm, fun y hy => hu y (fun h => hy h.symm)⟩
  loopless := ⟨by
    intro f h
    obtain ⟨x, hx, _⟩ := h
    exact hx rfl⟩

/-- The flip at site `x`: toggle the value of `f` at `x`. -/
def flipAt (f : α → Bool) (x : α) : α → Bool := Function.update f x (! f x)

/-
**Regularity.** Every MV assignment has exactly `Fintype.card α` neighbours
in the single-site flip graph — one flip per site.
-/

/-
**Connectivity.** The single-site flip graph is connected: any two MV
assignments are joined by a sequence of single flips.
-/

/-
**Corollary for the Miura-ori.** The flip graph of mountain–valley
assignments of the `m × n` Miura-ori is `(m+1)(n+1)`-regular.
-/

end MiuraFlip


