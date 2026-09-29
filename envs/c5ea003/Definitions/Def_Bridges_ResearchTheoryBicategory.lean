-- Prove2me | Definitions.Def_Bridges_ResearchTheoryBicategory
-- name    : Bridges_ResearchTheoryBicategory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T10:51:36.773928+00:00
-- url     : https://prove2.me/theorems/7e9e13de-2bf1-4733-8d36-15c5c8e9bc1d
-- title:
--   Aether Catalog definitions — Bridges_ResearchTheoryBicategory
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ResearchTheoryBicategory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ResearchTheoryBicategory.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_TheoryMorphisms
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A Locally Preordered 2-Category of Research Theories

This file constructs the 2-dimensional semantics of theory translation.
Research theories (carrier + ℕ-valued invariant) form the objects of a
locally preordered 2-category, where:

- **0-cells** are `ResearchTheory` instances,
- **1-cells** are `OrderedTheoryHom` morphisms (invariant-monotone and
  invariant-order-preserving maps),
- **2-cells** `OrderedTheoryHom2 f g` witness that morphism `g` uniformly
  dominates `f` at the invariant level.

## Mathematical discovery

Horizontal composition of 2-cells is NOT automatically valid for plain
`TheoryHom`: the axiom `∀ x, T.Inv x ≤ U.Inv (f.toFun x)` only relates
source and target invariants, but does not ensure that the function preserves
the invariant *order* on the target carrier. We isolate the precise
strengthening: `OrderedTheoryHom`, which adds
`inv_action_monotone : ∀ a b, T.Inv a ≤ T.Inv b → U.Inv (toFun a) ≤ U.Inv (toFun b)`.

We also observe that a **terminal object** does not exist in full generality
in this category. The monotonicity condition `T.Inv x ≤ U.Inv (f x)` requires
the target to have large enough invariants, so no single theory can receive a
morphism from every theory. Instead, we construct the **initial object**
(empty carrier) and a **canonical least embedding** into the universal `NatTheory`.

## Cross-domain connections

- **Category theory**: hom-preorders yield an order-enriched category / thin bicategory.
- **Abstract interpretation**: 2-cells compare approximations.
- **Program semantics**: interpretations as compilers, 2-cells as optimization certificates.
- **Proof theory**: one encoding dominates another if it certifies higher invariants.
-/


/-! ## §1. 2-Cells: Pointwise Invariant Domination -/

/-- A **2-cell** `TheoryHom2 f g` witnesses that morphism `g` uniformly
    dominates `f` at the invariant level: for every source element `x`,
    the invariant of `g(x)` is at least that of `f(x)` in the target. -/
def TheoryHom2 {T U : ResearchTheory} (f g : TheoryHom T U) : Prop :=
  ∀ x : T.Carrier, U.Inv (f.toFun x) ≤ U.Inv (g.toFun x)

/-! ## §2. Vertical Composition and Identity of 2-Cells -/

theorem TheoryHom2.refl {T U : ResearchTheory} (f : TheoryHom T U) :
    TheoryHom2 f f :=
  fun _ => le_refl _

theorem TheoryHom2.trans {T U : ResearchTheory} {f g h : TheoryHom T U} :
    TheoryHom2 f g → TheoryHom2 g h → TheoryHom2 f h :=
  fun hfg hgh x => le_trans (hfg x) (hgh x)

/-! ## §3. Right-Whiskering for plain TheoryHom -/


/-! ## §4. Ordered Theory Morphisms -/

/-- An **ordered theory morphism** strengthens `TheoryHom` with invariant
    order preservation: if `T.Inv a ≤ T.Inv b` then
    `U.Inv (f a) ≤ U.Inv (f b)`. This is the precise condition needed
    for horizontal composition of 2-cells. -/
structure OrderedTheoryHom (T U : ResearchTheory) extends TheoryHom T U where
  inv_action_monotone : ∀ a b : T.Carrier,
    T.Inv a ≤ T.Inv b → U.Inv (toFun a) ≤ U.Inv (toFun b)


def OrderedTheoryHom.id (T : ResearchTheory) : OrderedTheoryHom T T where
  toFun := _root_.id
  monotone_inv := fun _ => le_refl _
  inv_action_monotone := fun _ _ h => h

def OrderedTheoryHom.comp {T U V : ResearchTheory}
    (f : OrderedTheoryHom T U) (g : OrderedTheoryHom U V) :
    OrderedTheoryHom T V where
  toFun := g.toFun ∘ f.toFun
  monotone_inv := fun x => le_trans (f.monotone_inv x) (g.monotone_inv (f.toFun x))
  inv_action_monotone := fun _ _ hab =>
    g.inv_action_monotone _ _ (f.inv_action_monotone _ _ hab)




/-! ## §5. 2-Cells for Ordered Morphisms -/

def OrderedTheoryHom2 {T U : ResearchTheory}
    (f g : OrderedTheoryHom T U) : Prop :=
  ∀ x : T.Carrier, U.Inv (f.toFun x) ≤ U.Inv (g.toFun x)

theorem OrderedTheoryHom2.refl {T U : ResearchTheory}
    (f : OrderedTheoryHom T U) : OrderedTheoryHom2 f f :=
  fun _ => le_refl _

theorem OrderedTheoryHom2.trans {T U : ResearchTheory}
    {f g h : OrderedTheoryHom T U} :
    OrderedTheoryHom2 f g → OrderedTheoryHom2 g h → OrderedTheoryHom2 f h :=
  fun hfg hgh x => le_trans (hfg x) (hgh x)

/-! ## §6. Horizontal Composition of 2-Cells -/




/-! ## §7. Interchange Law -/


/-! ## §8. Hom-Categories are Preorders -/

instance TheoryHom.instPreorder' {T U : ResearchTheory} :
    Preorder (TheoryHom T U) where
  le f g := TheoryHom2 f g
  le_refl f := TheoryHom2.refl f
  le_trans _ _ _ := TheoryHom2.trans



instance OrderedTheoryHom.instPreorder' {T U : ResearchTheory} :
    Preorder (OrderedTheoryHom T U) where
  le f g := OrderedTheoryHom2 f g
  le_refl f := OrderedTheoryHom2.refl f
  le_trans _ _ _ := OrderedTheoryHom2.trans



/-! ## §9. Initial Theory -/

/-- The initial theory has empty carrier. There is a unique morphism
    FROM it to any theory (vacuously satisfying all conditions). -/
def InitialTheory : ResearchTheory where
  Carrier := Empty
  Inv := Empty.elim

def fromInitial (T : ResearchTheory) : TheoryHom InitialTheory T where
  toFun := Empty.elim
  monotone_inv := fun x => x.elim

theorem fromInitial_unique (T : ResearchTheory)
    (f : TheoryHom InitialTheory T) :
    f = fromInitial T := by
  cases f with
  | mk toFun monotone_inv =>
    have h : toFun = (fromInitial T).toFun := funext (fun x => x.elim)
    cases h
    rfl

instance initial_hom_subsingleton (T : ResearchTheory) :
    Subsingleton (TheoryHom InitialTheory T) :=
  ⟨fun f g => (fromInitial_unique T f).trans (fromInitial_unique T g).symm⟩



/-! ## §10. Canonical Embedding into NatTheory -/

/-- The natural number theory: carrier ℕ with identity invariant.
    Every theory embeds canonically into it. -/
def NatTheory : ResearchTheory where
  Carrier := ℕ
  Inv := _root_.id

/-- Canonical embedding of any theory T into NatTheory via the invariant. -/
def toNatTheory (T : ResearchTheory) : TheoryHom T NatTheory where
  toFun := T.Inv
  monotone_inv := fun _ => le_refl _


/-! ## §11. Nontrivial Example: Two Distinct Morphisms with a 2-Cell -/

/-- Source theory: Bool carrier with invariant values 1 and 2. -/
private def SrcEx : ResearchTheory where
  Carrier := Bool
  Inv := fun b => bif b then 2 else 1

/-- Target theory: Bool carrier with invariant values 5 and 10. -/
private def TgtEx : ResearchTheory where
  Carrier := Bool
  Inv := fun b => bif b then 10 else 5

/-- Low morphism: maps everything to `false` (invariant 5). -/
private def mLow : TheoryHom SrcEx TgtEx where
  toFun := fun _ => false
  monotone_inv := by intro x; cases x <;> simp [SrcEx, TgtEx]

/-- High morphism: maps everything to `true` (invariant 10). -/
private def mHigh : TheoryHom SrcEx TgtEx where
  toFun := fun _ => true
  monotone_inv := by intro x; cases x <;> simp [SrcEx, TgtEx]




/-! ## §12. Locally Thin Bicategory Structure -/


