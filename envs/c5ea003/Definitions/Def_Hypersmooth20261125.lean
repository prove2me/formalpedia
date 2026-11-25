-- Prove2me | Definitions.Def_Hypersmooth20261125
-- name    : Hypersmooth20261125
-- status  : Definition
-- author  : @username
-- created : 2026-11-25T14:15:45.481543+00:00
-- url     : https://prove2.me/theorems/10774ac0-a1a7-4e3a-8a96-6530dd5a784a
-- title:
--   Smoothness and hypersmoothness
-- statement:
--   Borel reductions preserve and reflect every pair. A smooth relation is classified by a measurable Cantor-space map. A hypersmooth relation is the increasing union of smooth relations.
-- source:
--   counterexamples-to-hypersmoothness.tex, Section 2. Supplied manuscript SHA-256 03093bc96808d915a59451a3d40499e92916b9ae136e5309dcc9065b86a4a603.

import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false

namespace HypersmoothCounterexamples

/-- A Borel map preserving and reflecting a relation on every pair. -/
def BorelReducible {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (D : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x y, E x y ↔ D (f x) (f y)

/-- A smooth relation has a Borel classifier taking values in Cantor space. -/
def Smooth {X : Type*} [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  ∃ q : X → (ℕ → Bool), Measurable q ∧ ∀ x y, E x y ↔ q x = q y

/-- Hypersmooth relations are exactly increasing unions of smooth relations. -/
def Hypersmooth {X : Type*} [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  ∃ F : ℕ → X → X → Prop,
    (∀ n, Smooth (F n)) ∧
    (∀ n x y, F n x y → F (n + 1) x y) ∧
    (∀ x y, E x y ↔ ∃ n, F n x y)

end HypersmoothCounterexamples


