-- Prove2me | solution 1 for MomentHierarchy.two_mul_card_le_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T06:54:49.229877+00:00
-- url     : https://prove2.me/submissions/182224e9-d205-44d1-8896-7a12d2da76c7

/-
# `MomentHierarchy.two_mul_card_le_second_moment`
Target `fb6a913f-f07a-4ff0-a6ae-2c5d9ad5a3f4` (Open; re-read live immediately before submitting).

ORDINARY PROOF — transitive `Theorems.` screen over the preamble's one bundle
(`Def_Logic_MomentHierarchy`) is CLEAN.

BINDERS — three identical WA rejections state the expected type verbatim:

    has type     ∀ {G} {X} [Group G] [MulAction G X] [Fintype G] [Finite X] [Nontrivial X], ...
    but expected ∀ {G} {X} [Group G] [Fintype G] [MulAction G X] [Finite X] [Nontrivial X], ...

Pure binder ORDER: `[Fintype G]` BEFORE `[MulAction G X]`.

MATHS. Second moment = Burnside applied to the PRODUCT action:
  1. `Nat.card (fixedBy X g) ^ 2 = Nat.card (fixedBy (X × X) g)` — the bundle RETAINS
     `fixedByProdEquiv`, so this is `Nat.card_congr` then `Nat.card_prod`.
  2. Burnside on `X × X` turns `∑ g` into `orbits(X²) * |G|`.
  3. `2 ≤ orbits(X²)`, because `⟦(x,x)⟧ ≠ ⟦(x,y)⟧` for `x ≠ y`.

`htrans` is UNUSED and that is correct: orbits(X²) ≥ 2 holds for ANY action on a nontrivial X,
since `g • x = x` and `g • x = y` would force `x = y`. Transitivity would be needed only for the
matching EQUALITY, not this lower bound.

THE REAL COST IS THE `Nat.card` BRIDGE, not the mathematics. Mathlib has NO `Nat.card` form of
Burnside — `sum_card_fixedBy_eq_card_orbits_mul_card_group` (Quotient.lean:262) is stated wholly in
`Fintype.card` and demands `[Fintype α] [∀ a, Fintype (fixedBy β a)] [Fintype Ω]`, none automatic
from `[Finite X]`. Bridging lemmas, read out of source:
  * `Nat.card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α` (Cardinal/Finite.lean:45)
  * `Fintype.ofFinite (α) [Finite α] : Fintype α` — NONCOMPUTABLE (EquivFin.lean:179), so `haveI`
  * `Ω` is FILE-LOCAL notation for `Quotient (orbitRel α β)` (Quotient.lean:200) — it does not
    exist outside that file and must be written out longhand here. CONFIRMED by compile: the
    longhand term IS what Burnside elaborates to, and `simp only [Nat.card_eq_fintype_card]`
    does fire under the sum's binder. The bridge works.
  * `Finite.one_lt_card_iff_nontrivial [Finite α] : 1 < Nat.card α ↔ Nontrivial α`
    (`Data/Finite/Card.lean:74`). NOT `Nat.one_lt_card_iff_nontrivial` — that name sits past
    `end Nat` inside `namespace ENat`, so it is about `ENat.card` and does not exist as written.
  * `smul_left_cancel (g) {x y} (h : g • x = g • y) : x = y` (`Action/Basic.lean:59`). The orbit
    relation resolves as `hg.1 : g • x = x`, `hg.2 : g • y = x` — the OPPOSITE side from my
    guess, so the conclusion needs a final `.symm`.
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MulAction MomentHierarchy


/-- **The target, verbatim.** -/
theorem solution {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] [Nontrivial X]
    (htrans : IsPretransitive G X) :
    2 * Nat.card G ≤ ∑ g : G, Nat.card (fixedBy X g) ^ 2 := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ g : G, Fintype (fixedBy (X × X) g) := fun g => Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitRel G (X × X))) := Fintype.ofFinite _
  -- step 1: each summand is a fixed-point count on the product
  have hsq : ∀ g : G, Nat.card (fixedBy X g) ^ 2 = Nat.card (fixedBy (X × X) g) := by
    intro g
    rw [Nat.card_congr (MomentHierarchy.fixedByProdEquiv g), Nat.card_prod, sq]
  -- step 2: Burnside on the product action
  have hburn : (∑ g : G, Nat.card (fixedBy (X × X) g))
      = Nat.card (Quotient (orbitRel G (X × X))) * Nat.card G := by
    simp only [Nat.card_eq_fintype_card]
    exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (X × X)
  -- step 3: a nontrivial X forces at least two orbits on X × X
  have hnt : Nontrivial (Quotient (orbitRel G (X × X))) := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    refine ⟨⟦(x, x)⟧, ⟦(x, y)⟧, ?_⟩
    intro h
    rw [Quotient.eq] at h
    obtain ⟨g, hg⟩ := h
    simp [Prod.ext_iff] at hg
    -- hg.1 : g • x = x  and  hg.2 : g • y = x, so cancellation gives y = x
    exact hxy (smul_left_cancel g (hg.2.trans hg.1.symm)).symm
  have h2 : 2 ≤ Nat.card (Quotient (orbitRel G (X × X))) :=
    Finite.one_lt_card_iff_nontrivial.mpr hnt
  calc 2 * Nat.card G
      ≤ Nat.card (Quotient (orbitRel G (X × X))) * Nat.card G :=
        Nat.mul_le_mul_right _ h2
    _ = ∑ g : G, Nat.card (fixedBy (X × X) g) := hburn.symm
    _ = ∑ g : G, Nat.card (fixedBy X g) ^ 2 := by
        exact Finset.sum_congr rfl (fun g _ => (hsq g).symm)
