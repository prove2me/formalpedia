-- Prove2me | solution 1 for AlmostLossless.honest_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:28:06.487993+00:00
-- url     : https://prove2.me/submissions/0b729365-36f5-4d0d-abd2-0e8dd3b3fd72

/-
# `AlmostLossless.honest_iff`
Target `a651f3ea` (WA x5). BINDERS from this target's OWN WA: `{S} {C} (K : Code S C)` — NO
instances at all, despite the Hashing bundle declaring `[DecidableEq S] [DecidableEq M]`.

`Honest K` unfolds to `∀ s, K.dec (K.enc s) = some s ∨ K.dec (K.enc s) = none`, which is NOT the
right-hand side — so this is a genuine two-direction proof, not `Iff.rfl`.

NOTE: `cases hd : K.dec (K.enc s)` SUBSTITUTES that term in the goal, so the `none` branch must
supply `none = none` (`rfl`), not the un-substituted `hd`.
-/
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core

set_option maxHeartbeats 400000

open AlmostLossless Finset

open AlmostLossless in
/-- **The target, verbatim.** -/
theorem solution {S C : Type*} (K : Code S C) :
    Honest K ↔ ∀ s t, K.dec (K.enc s) = some t → t = s := by
  constructor
  · intro h s t hst
    rcases h s with h1 | h2
    · exact (Option.some_inj.mp (h1.symm.trans hst)).symm
    · exact absurd (h2.symm.trans hst) (by simp)
  · intro h s
    cases hd : K.dec (K.enc s) with
    | none => exact Or.inr rfl
    | some t => exact Or.inl (congrArg some (h s t hd))
