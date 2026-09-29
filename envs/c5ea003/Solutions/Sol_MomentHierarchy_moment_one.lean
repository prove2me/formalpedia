-- Prove2me | solution 1 for MomentHierarchy.moment_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:52:48.812385+00:00
-- url     : https://prove2.me/submissions/a6a45154-2200-4968-96b9-9bfc9fbcda7b

/-
# `MomentHierarchy.moment_one`
Target `e46354e7` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

Burnside / orbit-counting. Mathlib carries it, but NOT in the target's shape (signature probed, not
guessed):

  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group :
    ∀ (α β) [Group α] [MulAction α β] [Fintype α] [∀ a, Fintype (fixedBy β a)]
      [Fintype (Quotient (orbitRel α β))],
    ∑ a, Fintype.card (fixedBy β a) = Fintype.card (Quotient (orbitRel α β)) * Fintype.card α

The target instead speaks of `Nat.card` and supplies only `[Finite X]`. So two bridges are needed:
a `Fintype X` obtained from `Finite X`, and `Nat.card_eq_fintype_card` to move between the two
cardinality notions. That instance gap is exactly what made the earlier direct `exact` fail.

BINDER ORDER is from the platform's expected type: [Group G] [Fintype G] [MulAction G X] [Finite X].
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false

open MulAction in
/-- **The target, verbatim.** -/
theorem solution {G : Type*} {X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] :
    ∑ g : G, Nat.card (fixedBy X g) = Nat.card (orbitRel.Quotient G X) * Nat.card G := by
  classical
  have : Fintype X := Fintype.ofFinite X
  simp only [Nat.card_eq_fintype_card]
  exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
