-- Prove2me | solution 1 for MomentHierarchy.pretransitive_iff_moment_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T07:13:47.839699+00:00
-- url     : https://prove2.me/submissions/204207a8-b70b-4f6b-90fb-ce9a845e2028

/-
# `MomentHierarchy.pretransitive_iff_moment_one_eq`
Target `8ef5e191-5494-4ca6-8b03-904427190039` (Open; re-read live immediately before submitting).

ORDINARY PROOF — `scripts/screen_bundles.sh` returns CLEAN (exit 0).

BINDERS — expected type, verbatim from the WA:

    ∀ {G} {X} [Group G] [Fintype G] [MulAction G X] [Finite X] [Nonempty X],
      IsPretransitive G X ↔ ∑ g, Nat.card ↑(fixedBy X g) = Nat.card G

Familiar family: [Fintype G] BEFORE [MulAction G X], [Finite X] once, [Nonempty X] last.

MATHS. Burnside at k = 1 gives `∑ g, |X^g| = |X/G| · |G|`. Since a group contains its identity,
`|G| > 0`, so the moment equals `|G|` exactly when the orbit count is 1 — and on a NONEMPTY carrier
"orbit count is 1" is exactly pretransitivity.

`[Nonempty X]` is load-bearing and only in the backward direction: on an empty carrier the quotient
is empty, the moment is 0, so `0 = |G|` fails, while the action is vacuously pretransitive.

PROBED, NOT GUESSED — read out of source:
  * `MulAction.pretransitive_iff_subsingleton_quotient (G α) :
       IsPretransitive G α ↔ Subsingleton (orbitRel.Quotient G α)` (Basic.lean:179).
    NOTE `variable (G α)` at Basic.lean:173 — BOTH arguments are EXPLICIT. Today's `hc.mapLe`
    failure was exactly this kind of arity surprise, so they are passed explicitly below.
  * `mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b ≠ 0) : a * b = b ↔ a = 1`
    (GroupWithZero/Basic.lean:305) — ℕ qualifies. NOT `mul_left_cancel₀`, which needs a field-like
    inverse and does not apply here.
  * `Nat.card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α` (Finite.lean:195).
  * `nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α` (Quot.lean:446).
  * `Nat.card_pos [Nonempty α] [Finite α] : 0 < Nat.card α` (Finite.lean:85).
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MulAction MomentHierarchy


/-- **The target, verbatim.** -/
theorem solution {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] [Nonempty X] :
    IsPretransitive G X ↔ ∑ g : G, Nat.card (fixedBy X g) = Nat.card G := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ g : G, Fintype (fixedBy X g) := fun g => Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitRel G X)) := Fintype.ofFinite _
  haveI : Nonempty (orbitRel.Quotient G X) := (nonempty_quotient_iff _).mpr inferInstance
  -- Burnside at k = 1
  have hburn : (∑ g : G, Nat.card (fixedBy X g))
      = Nat.card (orbitRel.Quotient G X) * Nat.card G := by
    simp only [Nat.card_eq_fintype_card]
    exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  -- cancel |G|, leaving "the orbit count is one"
  rw [hburn, mul_eq_right₀ hGne, MulAction.pretransitive_iff_subsingleton_quotient G X]
  constructor
  · intro hs
    exact Nat.card_eq_one_iff_unique.mpr ⟨hs, inferInstance⟩
  · intro h
    exact (Nat.card_eq_one_iff_unique.mp h).1
