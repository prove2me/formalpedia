-- Prove2me | Theorems.Thm_height_down_realize
-- name    : height_down_realize
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:26:10.624376+00:00
-- url     : https://prove2.me/theorems/1620b4df-08b7-42d5-a029-c1f37158f467
-- title:
--   Downward realizability of heights: if `α ≤ height w`, then some element `u ≤ w`
-- statement:
--   Downward realizability of heights: if `α ≤ height w`, then some element `u ≤ w`
--   has height exactly `α`.
--
--   ```lean
--   theorem height_down_realize(w : P) (α : Ordinal) (h : α ≤ height w) :
--       ∃ u, u ≤ w ∧ height u = α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AharoniKorman.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AharoniKorman.lean#L70

-- Thm stub generated from Probability/AharoniKorman.lean
import Mathlib
import Definitions.Def_Probability_AharoniKorman
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


variable {P : Type*} [Preorder P] [IsWellFounded P (· < ·)]

theorem height_down_realize(w : P) (α : Ordinal) (h : α ≤ height w) :
    ∃ u, u ≤ w ∧ height u = α := by sorry
