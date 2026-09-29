-- Prove2me | solution 1 for MomentHierarchy.sum_fixedPoints_pow_eq_orbits_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T07:02:48.122791+00:00
-- url     : https://prove2.me/submissions/e234525b-2116-4d31-bbff-062b340dcc2a

/-
# `MomentHierarchy.sum_fixedPoints_pow_eq_orbits_mul_card`
Target `34c897b0-8c09-429c-913e-772e0ee90a80` (Open; re-read live immediately before submitting).

ORDINARY PROOF — `scripts/screen_bundles.sh` returns CLEAN (exit 0): the preamble's one bundle
`Def_Logic_MomentHierarchy` has no `Theorems.` import anywhere in its closure.

BINDERS — three identical WA rejections state the expected type verbatim:

    has type     ∀ {G} {X} [Group G] [MulAction G X] [Fintype G] [Finite X] [Finite X] (k : ℕ), ...
    but expected ∀ {G} {X} [Group G] [Fintype G] [MulAction G X] [Finite X]            (k : ℕ), ...

TWO faults at once: the usual ORDER trap (`[MulAction G X]` before `[Fintype G]`), AND a
**duplicated `[Finite X]`** — the statement text carries it and the section variable supplies it, so
writing it out naively yields it twice. Write `[Finite X]` exactly ONCE, and `(k : ℕ)` last.

MATHS. This is the general-k moment identity, of which the theorem I just shipped (`fb6a913f`) is
the k=2 case. Same two steps:
  1. `Nat.card (fixedBy X g) ^ k = Nat.card (fixedBy (Fin k → X) g)` — the bundle RETAINS
     `fixedByPiEquiv`, so this is `Nat.card_congr` then `Nat.card_fun` then `Nat.card_fin`.
  2. Burnside on the k-tuple action turns `∑ g` into `orbits(Fin k → X) · |G|`.

PROBED, NOT GUESSED — read out of source:
  * `fixedByPiEquiv (g) : fixedBy (ι → X) g ≃ (ι → fixedBy X g)` — RETAINED by the bundle (line 63).
  * `Nat.card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α` (Cardinal/Finite.lean:242).
  * `Nat.card_fin (n) : Nat.card (Fin n) = n` (Cardinal/Finite.lean:138).
  * `sum_card_fixedBy_eq_card_orbits_mul_card_group` is stated wholly in `Fintype.card` and needs
    three `Fintype` instances, none automatic from `Finite` — same bridge as `fb6a913f`.
  * `orbitRel.Quotient` is an ABBREV (Defs.lean:341), so it is defeq to `Quotient (orbitRel ..)`.
    CAUTION: today's `Walk.mapLe` failure proved reducible does NOT mean simp/rw see through an
    abbrev. So the abbrev boundary is crossed by `calc`/`exact` (defeq-tolerant), never by rw/simp.
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MulAction MomentHierarchy


/-- **The target, verbatim.** -/
theorem solution {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] (k : ℕ) :
    ∑ g : G, Nat.card (fixedBy X g) ^ k
      = Nat.card (orbitRel.Quotient G (Fin k → X)) * Nat.card G := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ g : G, Fintype (fixedBy (Fin k → X) g) := fun g => Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitRel G (Fin k → X))) := Fintype.ofFinite _
  -- step 1: each summand is a fixed-point count on the space of k-tuples
  have hpow : ∀ g : G, Nat.card (fixedBy X g) ^ k = Nat.card (fixedBy (Fin k → X) g) := by
    intro g
    rw [Nat.card_congr (MomentHierarchy.fixedByPiEquiv g), Nat.card_fun, Nat.card_fin]
  -- step 2: Burnside on the k-tuple action
  have hburn : (∑ g : G, Nat.card (fixedBy (Fin k → X) g))
      = Nat.card (Quotient (orbitRel G (Fin k → X))) * Nat.card G := by
    simp only [Nat.card_eq_fintype_card]
    exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Fin k → X)
  -- the abbrev boundary is crossed HERE, by calc/defeq, not by a rewrite
  calc ∑ g : G, Nat.card (fixedBy X g) ^ k
      = ∑ g : G, Nat.card (fixedBy (Fin k → X) g) := Finset.sum_congr rfl (fun g _ => hpow g)
    _ = Nat.card (orbitRel.Quotient G (Fin k → X)) * Nat.card G := hburn
