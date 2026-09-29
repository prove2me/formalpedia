-- Prove2me | solution 1 for MiuraFlip.flipGraph_degree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:43:16.607931+00:00
-- url     : https://prove2.me/submissions/1ed043e7-4935-40fe-8510-c5e71bd82454

-- Sol generated from Applications/MiuraFlipGraph/FlipGraph.lean
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

/-
**Connectivity.** The single-site flip graph is connected: any two MV
assignments are joined by a sequence of single flips.
-/

/-
**Corollary for the Miura-ori.** The flip graph of mountain–valley
assignments of the `m × n` Miura-ori is `(m+1)(n+1)`-regular.
-/


open MiuraFlip in
theorem solution(f : α → Bool) :
    (flipGraph α).degree f = Fintype.card α := by
  -- By definition of neighborFinset, we know
  -- `neighborFinset f = Finset.univ.image (fun x => flipAt f x)`.
  have h_neighborFinset_eq : (flipGraph α).neighborFinset f = Finset.univ.image (fun x => flipAt f x) := by
    ext g; simp [flipGraph];
    constructor <;> intro h;
    · obtain ⟨ x, hx, hx' ⟩ := h;
      use x; ext y; by_cases hy : y = x <;> simp_all +decide [ flipAt ] ;
      · cases h : f x <;> cases h' : g x <;> aesop;
      · exact Classical.not_not.1 fun h => hy <| hx' y h;
    · unfold flipAt at h;
      obtain ⟨ x, rfl ⟩ := h; use x; simp +decide [ Function.update_apply ] ;
  rw [ SimpleGraph.degree, h_neighborFinset_eq, Finset.card_image_of_injective, Finset.card_univ ];
  intro x y h; have := congr_fun h x; have := congr_fun h y; simp_all +decide [ flipAt ] ;
  grind
