-- Prove2me | Definitions.Def_Novelty_ThinMonoidal
-- name    : Novelty_ThinMonoidal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:39.095304+00:00
-- url     : https://prove2.me/theorems/859d871a-3593-4bce-b187-e98a3e2d295d
-- title:
--   Aether Catalog definitions — Novelty_ThinMonoidal
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ThinMonoidal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ThinMonoidal.lean by skeleton subtraction
import Mathlib

/-!
# Coherence from thinness: when loops in composition cannot misbehave

This file develops the abstract engine behind the mission "Causal Loops in Category
Theory: when composition loops back".

The guiding idea of a *bicategory* / *monoidal category* is that composition (resp. the
tensor product) need not be associative *on the nose*: instead there is a specified
invertible `2`-cell — the **associator** — witnessing `(f ∘ g) ∘ h ≅ f ∘ (g ∘ h)`.
The price of this freedom is *coherence*: the associator must satisfy Mac Lane's
pentagon and triangle equations so that every way of re-bracketing a composite agrees.

The cleanest situation in which coherence is *free* is when the ambient category is
**thin**: there is at most one morphism between any two objects.  Then *every* diagram
of morphisms commutes, so a bare choice of tensor data automatically satisfies all the
coherence axioms.  Intuitively: the `2`-cells recording "how composition loops back" are
so rigid that no incoherence can arise.

## Main results

* `ThinCategory` — the class of categories with subsingleton hom-sets.
* `ThinCategory.thin` / `ThinCategory.hom_ext` — parallel morphisms coincide.
* `monoidalOfThin` — **any** `MonoidalCategoryStruct` on a thin category is a genuine
  `MonoidalCategory`: pentagon, triangle and all naturality squares hold for free.
* `ThinCategory.subsingleton_iso` — even isomorphisms are unique.
* `ThinCategory.associator_loop` — the "causal loop" statement: chasing the associator
  around the pentagon and back returns the identity.
-/

open CategoryTheory MonoidalCategory

namespace CausalLoops

universe v u

/-- A **thin** category: at most one morphism between any two objects.
Equivalently, a category whose hom-sets are subsingletons; equivalently, a preorder
viewed as a category.  In a thin category every diagram commutes. -/
class ThinCategory (C : Type u) [Category.{v} C] : Prop where
  /-- Any two parallel morphisms are equal. -/
  thin : ∀ {X Y : C} (f g : X ⟶ Y), f = g

namespace ThinCategory

variable {C : Type u} [Category.{v} C] [ThinCategory C]


/-- Hom-sets of a thin category are subsingletons. -/
instance subsingleton_hom (X Y : C) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => ThinCategory.thin f g⟩

/-- Even the *isomorphisms* between two objects of a thin category are unique: an
isomorphism carries no information beyond its existence. -/
instance subsingleton_iso (X Y : C) : Subsingleton (X ≅ Y) :=
  ⟨fun f g => by
    apply Iso.ext
    exact ThinCategory.thin _ _⟩

end ThinCategory

/-- **Coherence is free in a thin category.**

Given any choice of tensor data (`MonoidalCategoryStruct`) on a thin category, the
data automatically assembles into a genuine `MonoidalCategory`: the pentagon and
triangle identities, together with every naturality square, hold because parallel
morphisms in a thin category coincide.

This is the abstract form of the mission's claim that "every *coherent* loop-tolerant
algebraic structure forms a higher category": once the `2`-cells (here, all morphisms)
are rigid enough to be unique, no incoherence can occur. -/
def monoidalOfThin (C : Type u) [Category.{v} C] [ThinCategory C]
    [MonoidalCategoryStruct C] : MonoidalCategory C where
  tensorHom_def := by intros; apply ThinCategory.thin
  id_tensorHom_id := by intros; apply ThinCategory.thin
  tensorHom_comp_tensorHom := by intros; apply ThinCategory.thin
  whiskerLeft_id := by intros; apply ThinCategory.thin
  id_whiskerRight := by intros; apply ThinCategory.thin
  associator_naturality := by intros; apply ThinCategory.thin
  leftUnitor_naturality := by intros; apply ThinCategory.thin
  rightUnitor_naturality := by intros; apply ThinCategory.thin
  pentagon := by intros; apply ThinCategory.thin
  triangle := by intros; apply ThinCategory.thin

namespace ThinCategory

variable {C : Type u} [Category.{v} C] [ThinCategory C] [MonoidalCategoryStruct C]




end ThinCategory

end CausalLoops


