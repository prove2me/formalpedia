-- Prove2me | Definitions.Def_Bridges_InvariantProduct
-- name    : Bridges_InvariantProduct
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:08.577399+00:00
-- url     : https://prove2.me/theorems/e130aafd-cc65-4f57-8e44-664a5bd0ea57
-- title:
--   Aether Catalog definitions — Bridges_InvariantProduct
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InvariantProduct`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InvariantProduct.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Categorical Products for Invariant-Bearing Systems

This file establishes that systems equipped with a complexity/energy/valuation
functional form a category with genuine categorical products.

## Main Results

- `InvObj`: A structure pairing a carrier type with an invariant map `Inv : Carrier → α`.
- `InvHom`: Morphisms that are non-increasing with respect to invariants.
- `prodObj`: The product object using `max` on invariants.
- `prod_universal`: The full universal property of the categorical product.
- `max_prod_is_initial`: `max` is the least invariant making both projections morphisms.

## Mathematical Significance

The `max` invariant on products is not an arbitrary choice — it is the *optimal*
categorical product invariant for order-controlled morphisms:
- In thermodynamic language, `max` gives bottleneck energy.
- In automata theory, it models synchronized product complexity.
- In lattice reduction, it yields sup-norm height.
- In security, it tracks worst-case attack cost across composed protocols.

The universal property ensures that every future theorem about invariant-preserving
maps can be stated once and inherited by products automatically.
-/


/-! ## Core Structures -/

/-- An invariant-bearing object: a carrier type with a valuation/energy/complexity map. -/
structure InvObj (α : Type*) where
  Carrier : Type*
  Inv : Carrier → α

/-- A morphism between invariant-bearing objects: a function that does not increase the invariant.
    The orientation `B.Inv (toFun x) ≤ A.Inv x` makes morphisms "energy-dissipating" or
    "complexity non-increasing", which is natural for security/energy/height bounds. -/
structure InvHom {α : Type*} [Preorder α] (A B : InvObj α) where
  toFun : A.Carrier → B.Carrier
  monotone_inv : ∀ x, B.Inv (toFun x) ≤ A.Inv x

/-! ## Extensionality -/


/-! ## Identity and Composition -/

/-- The identity morphism on an invariant-bearing object. -/
def InvHom.id {α : Type*} [Preorder α] (A : InvObj α) : InvHom A A where
  toFun := _root_.id
  monotone_inv := fun _ => le_refl _

/-- Composition of invariant-bearing morphisms. -/
def InvHom.comp {α : Type*} [Preorder α] {A B C : InvObj α}
    (g : InvHom B C) (f : InvHom A B) : InvHom A C where
  toFun := g.toFun ∘ f.toFun
  monotone_inv := fun x => le_trans (g.monotone_inv (f.toFun x)) (f.monotone_inv x)

/-! ## Product Object -/

/-- The product of two invariant-bearing objects, with invariant given by `max`.
    This is the categorical product: `max` is the least invariant on `T × U`
    that makes both projections into morphisms. -/
def prodObj {α : Type*} [LinearOrder α] (T U : InvObj α) : InvObj α where
  Carrier := T.Carrier × U.Carrier
  Inv := fun p => max (T.Inv p.1) (U.Inv p.2)

/-! ## Projection Morphisms -/

/-- First projection from the product. The morphism condition holds because
    `T.Inv p.1 ≤ max (T.Inv p.1) (U.Inv p.2)`. -/
def fstHom {α : Type*} [LinearOrder α] (T U : InvObj α) :
    InvHom (prodObj T U) T where
  toFun := Prod.fst
  monotone_inv := fun _ => le_max_left _ _

/-- Second projection from the product. The morphism condition holds because
    `U.Inv p.2 ≤ max (T.Inv p.1) (U.Inv p.2)`. -/
def sndHom {α : Type*} [LinearOrder α] (T U : InvObj α) :
    InvHom (prodObj T U) U where
  toFun := Prod.snd
  monotone_inv := fun _ => le_max_right _ _

/-! ## Universal Pairing -/

/-- The universal lift into the product: given morphisms `f : S ⟶ T` and `g : S ⟶ U`,
    construct the unique morphism `S ⟶ T × U`. The invariant bound follows from
    `max_le` applied to the individual bounds `f.monotone_inv` and `g.monotone_inv`. -/
def prodLift {α : Type*} [LinearOrder α]
    {S T U : InvObj α} (f : InvHom S T) (g : InvHom S U) :
    InvHom S (prodObj T U) where
  toFun := fun x => (f.toFun x, g.toFun x)
  monotone_inv := fun x => max_le (f.monotone_inv x) (g.monotone_inv x)

/-! ## Commutation Laws -/



/-! ## Uniqueness -/

/-
Any morphism into the product that agrees with `f` on first components and `g` on
    second components must equal `prodLift f g`. This is the uniqueness half of the
    universal property.
-/

/-! ## Full Universal Property -/

/-
The full universal property of the categorical product: for any `S` with morphisms
    `f : S ⟶ T` and `g : S ⟶ U`, there exists a *unique* morphism `h : S ⟶ T × U`
    such that `π₁ ∘ h = f` and `π₂ ∘ h = g`.
-/

/-! ## Extensionality for Product Morphisms -/

/-
Two morphisms into a product are equal if they agree on both components.
-/

/-! ## Optimality of Max Invariant -/

/-
The `max` invariant is the *least* invariant on `T × U` making both projections
    into morphisms. This shows the product construction is not arbitrary but optimal:
    any other invariant that makes projections valid must dominate `max`.
-/

/-! ## Additive Product Variant -/


/-
In an ordered additive monoid with canonical ordering, the additive invariant
    dominates each component, making both projections into morphisms.
-/

/-! ## Comparison: Max vs Additive Product -/

/-
The `max` invariant is always dominated by the additive invariant when values are
    nonneg. This gives a comparison functor from max-products to additive-products.
-/

/-! ## Category Laws -/

/-
Left identity for composition.
-/

/-
Right identity for composition.
-/

/-
Associativity of composition.
-/


