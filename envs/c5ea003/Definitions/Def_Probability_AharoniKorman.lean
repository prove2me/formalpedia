-- Prove2me | Definitions.Def_Probability_AharoniKorman
-- name    : Probability_AharoniKorman
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:18.496779+00:00
-- url     : https://prove2.me/theorems/28cf938e-475b-427d-9cd4-f4e82076cc18
-- title:
--   Aether Catalog definitions — Probability_AharoniKorman
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AharoniKorman`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AharoniKorman.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Aharoni–Korman Theorem for Well-Founded FAC Posets

This file formalizes the statement of the Aharoni–Korman theorem in the setting of
well-founded posets with the *Finite Antichain Condition* (FAC): every antichain is finite.

The Aharoni–Korman theorem (also known as the "fishbone conjecture" in one of its forms)
concerns partitions of posets into chains and antichains. In the well-founded FAC setting
considered here we produce a single chain that meets every nonempty level set of the poset,
where the levels are indexed by the ordinal-valued *height* (well-founded rank) function.

## Main definitions

* `FAC P` : the finite antichain condition on a preorder `P`.
* `height x` : the ordinal well-founded rank of `x` with respect to `(· < ·)`.
* `levelSet α` : the set of elements of a given height `α`.

## Main statements

* `height_strict_mono` : the height is strictly monotone.
* `level_is_antichain`, `level_finite` : each level set is a finite antichain.
* `levels_disjoint`, `levels_cover` : the level sets partition the poset.
* `height_down_realize` : downward realizability of heights below a given element.
* `finite_chain_hits` : a finite family of nonempty levels can be met by a single chain.
* `wellFoundedFAC_aharoni_korman` : the main theorem — a single chain meets every
  nonempty level.
-/

/-- The Finite Antichain Condition: every antichain (with respect to the strict order `<`)
is finite. -/
class FAC (P : Type*) [Preorder P] : Prop where
  finite_antichain : ∀ s : Set P, IsAntichain (· < ·) s → s.Finite

variable {P : Type*} [Preorder P] [IsWellFounded P (· < ·)]

/-- The height of an element is its well-founded rank with respect to the strict order. -/
noncomputable def height (x : P) : Ordinal := IsWellFounded.rank (· < ·) x

/-- The set of elements of a given height `α`. -/
def levelSet (α : Ordinal) : Set P := {x : P | height x = α}







/-
Helper for `finite_chain_hits`: given a finite set `S` of ordinals all bounded by
`height w`, there is a chain lying entirely below `w` that meets every level in `S`.

The chain is built top-down: pick the largest ordinal `M` in `S`, realize it by some
`u ≤ w` (via `height_down_realize`), and recurse on `S.erase M` with the smaller element
`u`. Since heights are strictly monotone, the resulting elements form a descending chain.
-/


