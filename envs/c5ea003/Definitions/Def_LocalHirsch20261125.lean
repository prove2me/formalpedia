-- Prove2me | Definitions.Def_LocalHirsch20261125
-- name    : LocalHirsch20261125
-- status  : Definition
-- author  : @username
-- created : 2026-11-25T14:17:16.450805+00:00
-- url     : https://prove2.me/theorems/4b3afdf7-a44a-425f-bf37-ac8216e06670
-- title:
--   Local Hirsch length and Borel hyperfiniteness
-- statement:
--   The rationalized abelianized factors of the derived series detect finite Hirsch length of a solvable group. The local hypothesis applies to each finitely generated subgroup, which must contain a solvable finite-index subgroup of finite Hirsch length. Hyperfiniteness requires an increasing sequence of Borel equivalence relations with finite classes exhausting the orbit relation.
-- source:
--   hyperfiniteness-and-finite-hirsch-length.tex, Introduction and Section 2. Supplied manuscript SHA-256 3fc959f77eef8bd2c0ac1349f4d875e7c83ce8d168bc63c39b4df2fcbdd966e0.

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.RingTheory.Finiteness.Defs

set_option autoImplicit false

namespace LocalHirschHyperfinite

/-- The rationalization of the `n`th abelian factor of the derived series.
Abelianizing the `n`th derived subgroup quotients it by its own commutator subgroup. -/
abbrev RationalDerivedFactor (G : Type*) [Group G] (n : ℕ) :=
  TensorProduct ℤ ℚ (Additive (Abelianization (derivedSeries G n)))

/-- Finite Hirsch length for a solvable group. Solvability makes the
derived series terminate, so the sum of the finitely many ranks is finite. -/
def IsSolvableFiniteHirsch (G : Type*) [Group G] : Prop :=
  IsSolvable G ∧ ∀ n : ℕ, Module.Finite ℚ (RationalDerivedFactor G n)

def IsVirtuallySolvableFiniteHirsch (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsSolvableFiniteHirsch H

def IsLocallyVirtuallySolvableFiniteHirsch (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → IsVirtuallySolvableFiniteHirsch H

def BorelAction (G X : Type*) [Group G] [MulAction G X] [MeasurableSpace X] : Prop :=
  ∀ g : G, Measurable (fun x : X => g • x)

def orbitRel (G : Type*) {X : Type*} [Group G] [MulAction G X] (x y : X) : Prop :=
  ∃ g : G, g • x = y

def BorelEquivalence {X : Type*} [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  Equivalence E ∧ MeasurableSet {p : X × X | E p.1 p.2}

def IsHyperfinite {X : Type*} [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  BorelEquivalence E ∧
    ∃ F : ℕ → X → X → Prop,
      Monotone F ∧
      (∀ n, BorelEquivalence (F n) ∧ ∀ x, {y | F n x y}.Finite) ∧
      ∀ x y, E x y ↔ ∃ n, F n x y

end LocalHirschHyperfinite


