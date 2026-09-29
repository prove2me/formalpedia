-- Prove2me | solution 1 for UniformWitnessBound.completeFamily_missingTraceSize
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:49:52.718309+00:00
-- url     : https://prove2.me/submissions/205fce47-5664-42b0-afd2-b3f2ece9b7f7

-- Sol generated from Bridges/GraphTheory/UniformWitnessBound.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_UniformWitnessBound
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

open UniformWitnessBound

variable {n : ℕ}

/-! ## I. Definitions -/








/-! ## II. Basic facts about uniform families -/



/-! ## III. The combinatorial core: private facets are disjoint across members -/




/-! ## IV. The uniform witness bound -/


/-! ## V. The complete family and the saturated equality case -/





/-! ## VI. The trivial star construction -/




open UniformWitnessBound in
theorem solution{n d : ℕ} (hn : d + 2 ≤ n) :
    MissingTraceSize (completeFamily n d) d 0 := by
  intro A hA
  simp [privateFacets];
  intro D hDA hD_card
  have h_facet_deg : facetDeg (completeFamily n d) D ≥ 2 := by
    obtain ⟨x, hx⟩ : ∃ x : Fin n, x ∉ A := by
      contrapose! hn;
      simp_all +decide [ Finset.eq_univ_of_forall hn, completeFamily ];
    refine' Finset.one_lt_card.mpr ⟨ A, _, Insert.insert x D, _, _ ⟩ <;> simp_all +decide [ completeFamily ];
    · rw [ Finset.card_insert_of_notMem ( fun h => hx <| hDA h ), hD_card ];
    · grind;
  linarith
