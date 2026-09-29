-- Prove2me | Definitions.Def_Bridges_GraphTheory_UniformWitnessBound
-- name    : Bridges_GraphTheory_UniformWitnessBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:46.305009+00:00
-- url     : https://prove2.me/theorems/2c501753-c8ef-445f-a7fd-c9968b3c6275
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_UniformWitnessBound
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.UniformWitnessBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/UniformWitnessBound.lean by skeleton subtraction
import Mathlib
/-! # The Uniform Witness Bound (corrected)

This file formalizes the *uniform witness bound* for `(d+1)`-uniform set families
classified by their *missing-trace size*, together with a combinatorial proof of the
extremal inequality and the equality characterisation in the saturated (`s = 0`) regime.

## Trace / shattering background

The relevant trace–shattering vocabulary lives in `Catalog.Bridges.Foundations`
(`ConceptFamily`, `ConceptFamily.shatters`, the Sauer–Shelah growth function).  For a
`(d+1)`-uniform family `ℱ` the natural traces of a member `F ∈ ℱ` are its `d`-element
subsets ("facets").  A facet `D ⊆ F` is *present* as a trace exactly when some **other**
member `G ∈ ℱ` realises it as an intersection `G ∩ F = D`; equivalently when `D` is
contained in at least two members of `ℱ`.  It is a *missing trace* of `F` when `D` lies in
no other member, i.e. when `D` has facet–degree `1` ("a private facet of `F`").

The binomial manipulations rely on `Catalog.Bridges.CombinatorialBridge`
(`subset_card_le`, `finset_card_le_univ`) and Mathlib's `Nat.choose`, which already obeys
the convention `Nat.choose a b = 0` for `a < b`.

## Main definitions

* `IsUniform F d` — every member of `F` has exactly `d+1` elements.
* `facetDeg F D`  — the number of members of `F` containing the `d`-set `D`.
* `privateFacets F A d` — the missing traces of `A`: its `d`-subsets of facet–degree `1`.
* `MissingTraceSize F d s` — every member has exactly `s` missing traces.
* `W d s n` — the explicit witness bound `n.choose (d+1)` when `s = 0`, and
  `n.choose d / s` (Euclidean division) when `s ≥ 1`.
* `completeFamily n d` — all `(d+1)`-subsets of `[n]`, the saturated `s = 0` extremiser.
* `trivialStar n d` — all `(d+1)`-subsets through the fixed vertex `0`.

## Main results

* `uniform_witness_bound` : `F.card ≤ W d s n` for every `(d+1)`-uniform family with
  missing-trace size `s` (with `2 ≤ d`, `s ≤ d`, `2*(d+1) ≤ n`).  The `s ≥ 1` case is the
  genuine combinatorial step: the private facets of distinct members are *disjoint* sets of
  `d`-subsets, hence `F.card * s ≤ n.choose d`.
* `uniform_witness_eq_zero` : in the saturated regime `s = 0` equality `F.card = n.choose (d+1)`
  holds **iff** `F = completeFamily n d`.
* `completeFamily_*`, `trivialStar_*` : the two named constructions (the saturated
  extremiser and the trivial star) are genuine uniform families and we compute their
  cardinalities, witnessing non-vacuity of the bound.

## Scope note

The inequality `uniform_witness_bound` and the saturated equality case
`uniform_witness_eq_zero` are proved in full.  The fine equality classification across the
full range of `s` (the Chao–Xu–Yip–Zhang construction versus the trivial star, with the
threshold `⌊(d+1)/2⌋`) is the genuinely deep extremal content; here the relevant
constructions are defined and shown to be valid uniform families with explicit
cardinalities, but only the `s = 0` end of the classification is established as an `iff`.
-/

open Finset

namespace UniformWitnessBound

variable {n : ℕ}

/-! ## I. Definitions -/

/-- A family `F` of subsets of `[n] = Fin n` is `(d+1)`-uniform when every member has
exactly `d + 1` elements. -/
def IsUniform (F : Finset (Finset (Fin n))) (d : ℕ) : Prop :=
  ∀ A ∈ F, A.card = d + 1

/-- The facet–degree of a `d`-set `D`: the number of members of `F` containing `D`. -/
def facetDeg (F : Finset (Finset (Fin n))) (D : Finset (Fin n)) : ℕ :=
  (F.filter (fun A => D ⊆ A)).card

/-- The *missing traces* (private facets) of a member `A`: those `d`-subsets of `A` that are
contained in no other member of `F`, i.e. have facet–degree exactly `1`. -/
def privateFacets (F : Finset (Finset (Fin n))) (A : Finset (Fin n)) (d : ℕ) :
    Finset (Finset (Fin n)) :=
  (A.powersetCard d).filter (fun D => facetDeg F D = 1)

/-- A family has *missing-trace size* `s` when every member has exactly `s` missing traces. -/
def MissingTraceSize (F : Finset (Finset (Fin n))) (d s : ℕ) : Prop :=
  ∀ A ∈ F, (privateFacets F A d).card = s

/-- The explicit witness bound.  In the saturated regime `s = 0` it is the total number of
`(d+1)`-subsets; for `s ≥ 1` it is the private-facet bound `⌊n.choose d / s⌋`.  Euclidean
division and `Nat.choose` together encode the convention `binomial a b = 0` for `a < b`. -/
def W (d s n : ℕ) : ℕ := if s = 0 then n.choose (d + 1) else n.choose d / s

/-- The complete family: all `(d+1)`-subsets of `[n]`. -/
def completeFamily (n d : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard (d + 1)

/-- The trivial star through the vertex `0 : Fin n`: all `(d+1)`-subsets containing `0`. -/
def trivialStar (n d : ℕ) [NeZero n] : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard (d + 1)).filter (fun A => (0 : Fin n) ∈ A)

/-! ## II. Basic facts about uniform families -/



/-! ## III. The combinatorial core: private facets are disjoint across members -/




/-! ## IV. The uniform witness bound -/


/-! ## V. The complete family and the saturated equality case -/





/-! ## VI. The trivial star construction -/



end UniformWitnessBound


