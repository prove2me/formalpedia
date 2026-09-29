-- Prove2me | Definitions.Def_Probability_SeymourSecondNeighborhoodFinite
-- name    : Probability_SeymourSecondNeighborhoodFinite
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:09.359902+00:00
-- url     : https://prove2.me/theorems/e8ab3aac-3faf-4db3-bb7a-65dca6ab00e1
-- title:
--   Aether Catalog definitions — Probability_SeymourSecondNeighborhoodFinite
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SeymourSecondNeighborhoodFinite`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SeymourSecondNeighborhoodFinite.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Seymour's Second Neighborhood Conjecture: exhaustive finite verification

This file provides *machine-checked exhaustive verification* of Seymour's
Second Neighborhood Conjecture (SSNC) on all oriented graphs with a small
number of vertices.  It complements the human-insight proofs of the base cases
in `SeymourSecondNeighborhood.lean` (minimum out-degree ≤ 1, transitive
graphs, and functional graphs) by directly checking *every* oriented graph on
`3` and `4` labelled vertices.

An oriented graph on `Fin n` is encoded as a `Bool`-valued adjacency matrix
`adj : Fin n → Fin n → Bool`; the oriented condition is asymmetry
`isAsym adj`, which forbids both loops (`adj a a`) and digons
(`adj a b ∧ adj b a`).  We enumerate all `2^(n²)` such matrices with
`native_decide`.

These are *verification* results, not the insight-bearing theorems of the
companion file: they are here to give an independent, exhaustive check of the
small cases and to back the computational-evidence log.

`isSeymourB adj v` says the second out-neighborhood of `v` is at least as large
as its first out-neighborhood, matching `IsSeymour` of the companion file.
-/

open Finset

namespace Catalog.Probability.SeymourSNDFinite

variable {n : ℕ}

/-- First out-neighborhood as a `Finset` over `Fin n`. -/
abbrev outN (adj : Fin n → Fin n → Bool) (v : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => adj v w)

/-- Second out-neighborhood: vertices at directed distance exactly two. -/
abbrev secondN (adj : Fin n → Fin n → Bool) (v : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => w ≠ v ∧ ¬ adj v w ∧ ∃ x, adj v x ∧ adj x w)

/-- `v` is a Seymour vertex: `|N⁺⁺(v)| ≥ |N⁺(v)|`. -/
abbrev isSeymourB (adj : Fin n → Fin n → Bool) (v : Fin n) : Prop :=
  (outN adj v).card ≤ (secondN adj v).card

/-- Asymmetry: the oriented-graph condition (no loops, no digons). -/
abbrev isAsym (adj : Fin n → Fin n → Bool) : Prop :=
  ∀ a b, adj a b → ¬ adj b a



/-
-- !-- Lab Notes -- !--

## Hypothesis (Hypothesizer)
SSNC should hold with no exceptions on small vertex sets; if a counterexample
existed on n ≤ 4 vertices it would already refute the conjecture, so an
exhaustive check is a strong falsification test.

## Experiment (Experimenter)
We enumerate every Bool adjacency matrix on Fin 3 (2⁹ = 512 matrices) and Fin 4
(2¹⁶ = 65536 matrices), filter to the asymmetric (oriented) ones, and confirm
each has a Seymour vertex. Both checks pass via `native_decide`.

## Analysis (Analyst)
No counterexample exists on ≤ 4 vertices, consistent with the base-case proofs
in the companion file (every such small oriented graph has a vertex of
out-degree ≤ 1, so `exists_seymour_of_min_outdeg_le_one` already covers them).
The enumeration for n = 5 (2²⁵ matrices) is beyond a cheap `native_decide`
budget and is deliberately not attempted here.

## Critique (Critic)
These are exhaustive finite verifications (`native_decide`, hence the
`Lean.ofReduceBool` reduction), NOT the project's insight-bearing theorems —
those live in `SeymourSecondNeighborhood.lean` and use case analysis and
well-foundedness. Presented honestly as an independent finite cross-check.

## Synthesis (PI)
The finite verification and the structural base-case proofs agree, raising
confidence that the difficulty of SSNC genuinely begins only once minimum
out-degree ≥ 2 forces graphs with more vertices.
-/

end Catalog.Probability.SeymourSNDFinite


