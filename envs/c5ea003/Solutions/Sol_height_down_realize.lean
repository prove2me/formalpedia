-- Prove2me | solution 1 for height_down_realize
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:53:35.072911+00:00
-- url     : https://prove2.me/submissions/d4b98ef2-afe9-44d0-986b-0db46cb9623b

-- Sol generated from Probability/AharoniKorman.lean
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



/-- The height is strictly monotone: `x < y` implies `height x < height y`. -/
theorem height_strict_mono {x y : P} (h : x < y) : height x < height y := by
  convert IsWellFounded.rank_lt_of_rel h using 1






/-
Helper for `finite_chain_hits`: given a finite set `S` of ordinals all bounded by
`height w`, there is a chain lying entirely below `w` that meets every level in `S`.

The chain is built top-down: pick the largest ordinal `M` in `S`, realize it by some
`u ≤ w` (via `height_down_realize`), and recurse on `S.erase M` with the smaller element
`u`. Since heights are strictly monotone, the resulting elements form a descending chain.
-/





theorem solution(w : P) (α : Ordinal) (h : α ≤ height w) :
    ∃ u, u ≤ w ∧ height u = α := by
  induction' h : height w using Ordinal.induction with β ih generalizing w;
  by_cases hαβ : α < β;
  · -- Since α < β, there exists some b < w such that α ≤ height b.
    obtain ⟨b, hb₁, hb₂⟩ : ∃ b < w, α ≤ height b := by
      contrapose! hαβ;
      convert IsWellFounded.rank_eq ( · < · ) w |> le_of_eq |> le_trans <| ?_;
      · exact h.symm;
      · refine' ciSup_le' _;
        exact fun i => Order.succ_le_of_lt ( hαβ _ i.2 );
    exact Exists.elim (ih _ (height_strict_mono hb₁ |> lt_of_lt_of_le <| h.le) _ hb₂ rfl)
      fun u hu => ⟨u, hu.1.trans hb₁.le, hu.2⟩
  · grind +splitIndPred
