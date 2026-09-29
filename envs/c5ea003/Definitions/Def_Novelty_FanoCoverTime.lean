-- Prove2me | Definitions.Def_Novelty_FanoCoverTime
-- name    : Novelty_FanoCoverTime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:09.761203+00:00
-- url     : https://prove2.me/theorems/2051f468-f950-4b9a-8771-5c1ae5057dad
-- title:
--   Aether Catalog definitions — Novelty_FanoCoverTime
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FanoCoverTime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FanoCoverTime.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Coupon-collector cover time: the Fano plane vs. uniform 3-subsets

This file formalizes the *coupon collector cover time* of a finite family of blocks over
the ground set `Fin 7`, computed via inclusion–exclusion, and compares two families:

* `fanoLines`, the seven lines of the **Fano plane** (the unique `2-(7,3,1)` design), and
* `uniformThreeSubsets`, *all* `35` three-element subsets of `Fin 7`.

## The model

We draw a uniformly random block at each step; a point `p` is *covered* once some drawn
block contains it, and the **cover time** is the first step at which every point has been
covered.  Writing `τ_p` for the first time a block containing `p` is drawn, the cover time is
`max_p τ_p`, and a standard inclusion–exclusion over the points gives

`expCoverTime B = ∑_{∅ ≠ S ⊆ Fin 7} (-1)^{|S|+1} · |B| / coverCount B S`,

where `coverCount B S` is the number of blocks that meet `S`.  We take this
inclusion–exclusion expression as the **definition** of `expCoverTime`.

## Main results

* `fanoLines_card`, `uniformThreeSubsets_card`: the two families have `7` and `35` blocks.
* `fano_pair_unique_line`: any two distinct points lie on exactly one Fano line (the `2-(7,3,1)`
  property).
* `expCoverTime_uniformThreeSubsets_eq`: `expCoverTime uniformThreeSubsets = 85691/15810`.
* `expCoverTime_fano_eq`: `expCoverTime fanoLines = 163/30`.
* `fano_slower_than_uniform`: `85691/15810 < 163/30`, i.e. the Fano family has the *larger*
  expected cover time.  The `2-(7,3,1)` structure induces positive correlations between coverage
  events (covering one point makes its collinear partners more likely to be covered), which slows
  the collector relative to the more independent uniform 3-subsets.

## Implementation note

`uniformThreeSubsets` is defined as the (computable) list of all length-`3` sublists of
`List.finRange 7`, each turned into a `Finset`.  This is exactly the collection of `3`-element
subsets of `Fin 7`; we use this computable form (rather than `Finset.toList` of a filtered
powerset, which is noncomputable) so that the finite computations can be discharged by
`native_decide`.
-/

open Finset

/-- `coverCount B S` is the number of blocks of `B` that have nonempty intersection with `S`. -/
def coverCount (B : List (Finset (Fin 7))) (S : Finset (Fin 7)) : ℕ :=
  B.countP (fun b => decide (b ∩ S).Nonempty)

/-- The expected cover time of the block family `B`, defined by inclusion–exclusion over the
nonempty subsets `S` of `Fin 7`:
`expCoverTime B = ∑_{∅ ≠ S} (-1)^{|S|+1} · |B| / coverCount B S`. -/
def expCoverTime (B : List (Finset (Fin 7))) : ℚ :=
  ∑ S ∈ ((Finset.univ : Finset (Fin 7)).powerset.filter (fun S => S.Nonempty)),
    (-1 : ℚ) ^ (S.card + 1) * (B.length : ℚ) / (coverCount B S : ℚ)

/-- The seven lines of the Fano plane, in the standard cyclic construction
`{i, i+1, i+3}` (mod `7`). -/
def fanoLines : List (Finset (Fin 7)) :=
  [{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {4, 5, 0}, {5, 6, 1}, {0, 2, 6}]

/-- All `3`-element subsets of `Fin 7`, as a list of `Finset`s.  Implemented computably as the
length-`3` sublists of `List.finRange 7` mapped to `Finset`s; this is precisely the family
`(Finset.univ : Finset (Fin 7)).powerset.filter (·.card = 3)`. -/
def uniformThreeSubsets : List (Finset (Fin 7)) :=
  ((List.finRange 7).sublistsLen 3).map (fun l => l.toFinset)


