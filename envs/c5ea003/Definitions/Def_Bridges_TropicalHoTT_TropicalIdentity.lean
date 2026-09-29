-- Prove2me | Definitions.Def_Bridges_TropicalHoTT_TropicalIdentity
-- name    : Bridges_TropicalHoTT_TropicalIdentity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:28.082175+00:00
-- url     : https://prove2.me/theorems/793ef913-a51e-406f-b626-d4afbc61226a
-- title:
--   Aether Catalog definitions — Bridges_TropicalHoTT_TropicalIdentity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalHoTT.TropicalIdentity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalHoTT/TropicalIdentity.lean by skeleton subtraction
import Mathlib
/-
# Tropical Path-Indiscernibility as an Identity Shadow

This file establishes the tropical analogue of path-indiscernibility from
Homotopy Type Theory. In classical HoTT, identity of points is captured
by path types; here we replace paths with min-plus equidistance relations.

Two points in a finite weighted space are "tropically indiscernible" if they
have identical distance profiles to all other points. We prove this is an
equivalence relation, and that it coincides with equality under a separation
axiom — giving a concrete, decidable replacement for identity types.

## Main results

* `tropicallyIndiscernible_refl` — reflexivity
* `tropicallyIndiscernible_symm` — symmetry
* `tropicallyIndiscernible_trans` — transitivity
* `tropicallyIndiscernible_eq_of_separating` — coincides with equality under separation
* `tropicallyIndiscernible_equivalence` — bundled equivalence relation
* `tropicallyIndiscernible_decidable` — decidability on finite types
-/


/-! ## Core Definitions -/

/-- The equidistance profile of a point `x` in a weighted space.
    This is the tropical shadow of a "loop space at x": the function recording
    how x interacts with every other point via distance. -/
def profile {α : Type*} (d : α → α → ℝ) (x : α) : α → ℝ := fun z => d x z

/-- Two points are tropically indiscernible if they have identical distance
    profiles — they interact identically with every other point in the space.
    This is the tropical analogue of path-connectedness / identity. -/
def TropicallyIndiscernible {α : Type*} (d : α → α → ℝ) (x y : α) : Prop :=
  ∀ z, d x z = d y z

/-- A distance function is separating if tropical indiscernibility implies equality.
    This is the tropical analogue of the identity of indiscernibles. -/
def IsSeparating {α : Type*} (d : α → α → ℝ) : Prop :=
  ∀ x y, (∀ z, d x z = d y z) → x = y


/-! ## Equivalence Relation Theorems -/

/-
Tropical indiscernibility is reflexive: every point has the same distance
    profile as itself. This is the tropical analogue of `refl` for paths.
-/

/-
Tropical indiscernibility is symmetric: if x is indiscernible from y,
    then y is indiscernible from x. Tropical analogue of path inversion.
-/

/-
Tropical indiscernibility is transitive: if x ≈ y and y ≈ z then x ≈ z.
    Tropical analogue of path concatenation.
-/

/-
Under a separation axiom, tropical indiscernibility coincides with equality.
    This is the tropical identity of indiscernibles: the fundamental bridge between
    the tropical shadow and actual mathematical identity.
-/

/-
Tropical indiscernibility as a bundled equivalence relation.
-/

/-
Profile equality is equivalent to tropical indiscernibility.
-/

/-! ## Decidability -/

/-
Tropical indiscernibility is decidable on finite types with decidable
    distance equality. This is a key computational advantage of the tropical
    shadow over classical path types.
-/
instance tropicallyIndiscernible_decidable
    {α : Type*} [Fintype α] [DecidableEq α]
    (d : α → α → ℝ) [DecidableEq ℝ] (x y : α) :
    Decidable (TropicallyIndiscernible d x y) :=
  Fintype.decidableForallFintype

/-! ## Natural number version -/

/-- Tropical indiscernibility for ℕ-valued distance functions.
    This version is fully decidable without any additional instances. -/
def TropicallyIndiscernibleNat {α : Type*} (d : α → α → ℕ) (x y : α) : Prop :=
  ∀ z, d x z = d y z





instance tropicallyIndiscernibleNat_decidable
    {α : Type*} [Fintype α] [DecidableEq α]
    (d : α → α → ℕ) (x y : α) :
    Decidable (TropicallyIndiscernibleNat d x y) :=
  Fintype.decidableForallFintype


