-- Prove2me | Definitions.Def_Logic_PushoutHIT
-- name    : Logic_PushoutHIT
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:06:38.182984+00:00
-- url     : https://prove2.me/theorems/ebd1d9f8-372b-4e5e-a0c7-dea2b9601235
-- title:
--   Aether Catalog definitions — Logic_PushoutHIT
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PushoutHIT`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PushoutHIT.lean by skeleton subtraction
import Mathlib
/-
# Pushout as a Higher Inductive Type Surrogate

Defines a pushout via Lean's quotient types, proving recursion and uniqueness.

## Relationship to catalog
- Inspired by `HoTT.SuspensionData` from `Logic.HoTT.Univalence`
- Connects to `fundamental_theorem_oracle'` as a verified recursor construction

## What is genuinely new
- `Pushout`: concrete quotient-based HIT surrogate
- `pushout_rec_unique`: verified universal property
-/


universe u

namespace HoTTFound

/-! ## Pushout relation -/

/-- Generated equivalence relation on `B ⊕ C` identifying `inl (f a)` with `inr (g a)`. -/
inductive PushoutRel {A B C : Type u} (f : A → B) (g : A → C) :
    B ⊕ C → B ⊕ C → Prop
  | glue : ∀ a, PushoutRel f g (Sum.inl (f a)) (Sum.inr (g a))
  | refl : ∀ x, PushoutRel f g x x
  | symm : ∀ {x y}, PushoutRel f g x y → PushoutRel f g y x
  | trans : ∀ {x y z}, PushoutRel f g x y → PushoutRel f g y z → PushoutRel f g x z

/-- The pushout of `f : A → B` and `g : A → C`. -/
def Pushout {A B C : Type u} (f : A → B) (g : A → C) : Type u :=
  Quot (PushoutRel f g)

/-! ## Canonical maps -/

def Pushout.inl {A B C : Type u} {f : A → B} {g : A → C} (b : B) : Pushout f g :=
  Quot.mk _ (Sum.inl b)

def Pushout.inr {A B C : Type u} {f : A → B} {g : A → C} (c : C) : Pushout f g :=
  Quot.mk _ (Sum.inr c)


/-! ## Recursion principle -/

/-- The sum eliminator used in pushout recursion. -/
def pushoutSumElim {B C X : Type u} (iB : B → X) (iC : C → X) : B ⊕ C → X
  | Sum.inl b => iB b
  | Sum.inr c => iC c

/-- Recursion for pushouts: given compatible maps, produce a map out of the pushout. -/
def pushout_rec {A B C X : Type u} {f : A → B} {g : A → C}
    (iB : B → X) (iC : C → X)
    (comm : ∀ a, iB (f a) = iC (g a)) :
    Pushout f g → X := by
  apply Quot.lift (pushoutSumElim iB iC)
  intro x y hrel
  induction hrel with
  | glue a => exact comm a
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2



/-! ## Universal property -/

/-
**Universal property of the pushout.**
    The recursor produces the unique map satisfying the boundary equations.

    This is the characteristic property: the pushout is the universal cocone
    for the span `B ← A → C`.
-/

/-! ## Pushout of identity maps -/

/-
Gluing along identity maps collapses the pushout.
-/

/-! ## Functoriality -/


end HoTTFound


