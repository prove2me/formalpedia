-- Prove2me | solution 2 for MomentHierarchy.partitionCount_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T04:49:35.567095+00:00
-- url     : https://prove2.me/submissions/0626dc2e-b45a-4f06-b13b-c74cf7da595c

/-
# `MomentHierarchy.partitionCount_one`
Target `926076dc` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`partitionCount k = Nat.card (Setoid (Fin k))` counts the equivalence relations on a `k`-element
set, i.e. the `k`-th Bell number. Verified by exhaustive enumeration: the counts for k = 0..5 are
1, 1, 2, 5, 15, 52, matching the Bell sequence with NO indexing shift.

`decide` IS UNAVAILABLE HERE and no tactic gets around that: `partitionCount` is noncomputable,
and Lean synthesises none of `Fintype (Setoid (Fin 1))`, `DecidableEq (Setoid (Fin 2))`,
`Subsingleton (Setoid (Fin 1))` or `Unique (Setoid (Fin 1))`. All four were probed and all four
fail, so every `Fintype.card` route is closed and the subsingleton property must be proved by hand.

PROBED, NOT GUESSED:
  * `Nonempty (Setoid (Fin 1))` DOES synthesise (via `bot_nonempty`), so `Nat.card_unique` gets
    its instance; `Inhabited` does not, but is not needed.
  * `Setoid.refl` takes the setoid as an INSTANCE argument, not an explicit one, so the accessor
    that works on a bound hypothesis is `t.iseqv.refl a`, not `t.refl a`.
  * `Setoid.ext : (∀ a b, s a b ↔ t a b) → s = t`
  * `Nat.card_unique : [Nonempty α] → [Subsingleton α] → Nat.card α = 1`
  * `Subsingleton (Fin 1)` synthesises as `Fin.subsingleton_one`.
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy
import Definitions.Def_Logic_MomentHierarchyBell

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MomentHierarchy

/-- There is only one equivalence relation on a one-element type: two of them agree pointwise,
because every pair of points of `Fin 1` is equal and both relations are reflexive. -/
theorem setoid_fin_one_subsingleton : Subsingleton (Setoid (Fin 1)) := by
  constructor
  intro s t
  apply Setoid.ext
  intro a b
  have hab : a = b := Subsingleton.elim a b
  subst hab
  exact ⟨fun _ => t.iseqv.refl a, fun _ => s.iseqv.refl a⟩

/-- **The target, verbatim.** -/
theorem solution : partitionCount 1 = 1 := by
  haveI := setoid_fin_one_subsingleton
  show Nat.card (Setoid (Fin 1)) = 1
  exact Nat.card_unique
