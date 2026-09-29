-- Prove2me | Definitions.Def_Tropical_MagmaMonoid_Transformation
-- name    : Tropical_MagmaMonoid_Transformation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:12.127278+00:00
-- url     : https://prove2.me/theorems/4e49ff84-5bc8-4986-8cb8-9284aa6ac768
-- title:
--   Aether Catalog definitions — Tropical_MagmaMonoid_Transformation
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.MagmaMonoid.Transformation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/MagmaMonoid/Transformation.lean by skeleton subtraction
import Mathlib

/-!
# The magma monoid as a transformation monoid

A formalization of the pairmorph viewpoint from Baiduk and Kozerenko,
*Transformation Semigroup Perspective on the Magma Monoid* (2026).
-/

namespace MagmaMonoid

/-- A binary operation on `X`. -/
abbrev Operation (X : Type*) := X → X → X

/-- The product of binary operations defining the magma monoid. -/
def product {X : Type*} (f g : Operation X) : Operation X :=
  fun a b ↦ g (f a b) (f b a)

/-- The left-zero operation, which is the identity of the magma monoid. -/
def leftZero {X : Type*} : Operation X := fun a _ ↦ a

/-- The right-zero operation. -/
def rightZero {X : Type*} : Operation X := fun _ b ↦ b

/-- Reversal of an ordered pair. -/
def swap {X : Type*} (p : X × X) : X × X := (p.2, p.1)

/-- The pairmorph transformation induced by a binary operation. -/
def pairmorph {X : Type*} (f : Operation X) : X × X → X × X :=
  fun p ↦ (f p.1 p.2, f p.2 p.1)

/-- Transformations that commute with reversal of ordered pairs. -/
def IsPairmorph {X : Type*} (T : X × X → X × X) : Prop :=
  Function.Commute T swap

/-- The image of the pairmorph transformation. -/
def pairImage {X : Type*} (f : Operation X) : Set (X × X) :=
  Set.range (pairmorph f)

/-- The image under the pairmorph transformation of diagonal pairs. -/
def diagonalImage {X : Type*} (f : Operation X) : Set (X × X) :=
  Set.range (fun x ↦ pairmorph f (x, x))

/-- Diagonal points occurring anywhere in the pairmorph image. -/
def commutativeImage {X : Type*} (f : Operation X) : Set (X × X) :=
  pairImage f ∩ Set.range (fun x ↦ (x, x))

/-- Regularity in the magma monoid. -/
def IsRegular {X : Type*} (f : Operation X) : Prop :=
  ∃ g : Operation X, product (product f g) f = f












/-- Reversing the arguments of an operation. -/
def opposite {X : Type*} (f : Operation X) : Operation X :=
  fun a b ↦ f b a







end MagmaMonoid


