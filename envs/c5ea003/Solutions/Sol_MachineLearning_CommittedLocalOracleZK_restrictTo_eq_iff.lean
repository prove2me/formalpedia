-- Prove2me | solution 1 for MachineLearning.CommittedLocalOracleZK.restrictTo_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T06:03:30.07939+00:00
-- url     : https://prove2.me/submissions/0c4af840-d962-4949-80f3-e1fba2d27b35

/-
# `MachineLearning.CommittedLocalOracleZK.restrictTo_eq_iff`
Target `8b9243cd` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.
(Chain screened: the bundle's `Definitions.` closure contains NO `Theorems.` import.)

    restrictTo T f = fun i => if i ∈ T then some (f i) else none

Claim: `restrictTo T f = restrictTo T g ↔ ∀ i ∈ T, f i = g i`.

Forward: apply the equality of functions at an `i ∈ T`; both branches take the `some` case, giving
`some (f i) = some (g i)`, and `some` is injective.
Backward: funext, then split on `i ∈ T`. In `T` the hypothesis applies; outside it both sides are
`none` definitionally.

BINDERS — the five WA on this target are ALL binder mismatches, and the rejection prints the
expected type verbatim:

    has type     ∀ {I} {A} [DecidableEq I] [Fintype I] [DecidableEq A] [AddCommGroup A]
                   [DecidableEq I] (T : Finset I) (f g : I → A), ...
    but expected ∀ {I} {A} [DecidableEq I] (T : Finset I) (f g : I → A), ...

Note `DecidableEq I` appears TWICE in the rejected version — once pulled in from the file's
`variable` lines and once from the statement's own binder. The bundle declares
`variable [Fintype I] ... [AddCommGroup A]` FURTHER DOWN the file than this statement, so none of
those are in scope here; only the type variables from line 91 are. Hence: two implicit types, one
instance, three explicit arguments.
-/
import Mathlib
import Definitions.Def_MachineLearning_CommittedLocalOracleZK

set_option autoImplicit false
set_option maxHeartbeats 400000

open MachineLearning.CommittedLocalOracleZK in
/-- **The target, verbatim.** -/
theorem solution {I A : Type*} [DecidableEq I] (T : Finset I) (f g : I → A) :
    restrictTo T f = restrictTo T g ↔ ∀ i ∈ T, f i = g i := by
  constructor
  · intro h i hi
    have := congrFun h i
    simp only [restrictTo, if_pos hi, Option.some.injEq] at this
    exact this
  · intro h
    funext i
    simp only [restrictTo]
    by_cases hi : i ∈ T
    · simp [hi, h i hi]
    · simp [hi]
