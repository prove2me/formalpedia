-- Prove2me | Definitions.Def_NoUniversalFSigma261031052
-- name    : NoUniversalFSigma261031052
-- status  : Definition
-- author  : @username
-- created : 2026-10-23T06:24:39.851854+00:00
-- url     : https://prove2.me/theorems/a90d5493-2197-4e8f-993e-c8f25cc3c0ea
-- title:
--   $F_\sigma$ sets, measurable reductions, and real $\ell_2$ coset relations
-- statement:
--   The ambient real Hilbert space $\ell_2$ consists of square-summable real sequences with its norm topology. A set is $F_\sigma$ exactly when it is a countable union of closed sets, and a relation is $F_\sigma$ when its graph has that property in the product topology.
--
--   A map is Baire measurable when every open preimage has the Baire property, and Borel measurable when every open preimage is Borel for the given topology. A reduction $f$ of $E$ to $F$ satisfies $E(x,x')\iff F(f(x),f(x'))$ for every pair of points. For a real linear subspace $H\subseteq\ell_2$, the coset relation is $xE_Hx'\iff x-x'\in H$.
--
--   Universality means admitting a Borel measurable reduction from every $F_\sigma$ equivalence relation on every Polish space represented in the ordinary type universe. These definitions specify the common language of the targets; they do not assume a nonuniversality theorem.
-- source:
--   Ruijun Wang, There is no universal F_sigma equivalence relation, arXiv:2610.31052v1 (22 October 2026), Sections 2.1–2.3, https://arxiv.org/html/2610.31052v1#S2

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.MetricSpace.Polish

/-!
# Definitions for Theorem 1.1 of arXiv:2610.31052

The topology on the real Hilbert space `RealL2` is its native norm topology.
The property of Baire is expressed using Mathlib's `BaireMeasurableSet`.
All Borel measurability assertions use the Borel sigma algebras of the
specified topologies explicitly.
-/

namespace NoUniversalFSigma

/-- The real Hilbert space of square-summable sequences, indexed by the naturals. -/
abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2

/-- A countable union of closed subsets of the given topological space. -/
def IsFSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ s = ⋃ n, C n

/-- A binary relation whose graph is a countable union of closed sets. -/
def IsFSigmaRelation {X : Type*} [TopologicalSpace X] (E : X → X → Prop) : Prop :=
  IsFSigma {p : X × X | E p.1 p.2}

/-- A function is Baire measurable if every inverse image of an open set
has the property of Baire. This does not mean the Baire sigma algebra. -/
def IsBaireMeasurable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U)

/-- Borel measurability for the specified domain and codomain topologies. -/
def IsBorelMeasurable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  @Measurable X Y (borel X) (borel Y) f

/-- A reduction preserves and reflects the two binary relations. -/
def IsReduction {X Y : Type*} (f : X → Y) (E : X → X → Prop)
    (F : Y → Y → Prop) : Prop :=
  ∀ x y, E x y ↔ F (f x) (f y)

/-- The coset equivalence relation induced by a real linear subspace of `RealL2`. -/
def CosetRelation (H : Submodule ℝ RealL2) (x y : RealL2) : Prop :=
  x - y ∈ H

/-- Universality among F-sigma equivalence relations on Polish spaces,
with respect to Borel reductions. -/
def IsUniversalFSigma {Y : Type} [TopologicalSpace Y] (F : Y → Y → Prop) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] (E : X → X → Prop),
    Equivalence E → IsFSigmaRelation E →
      ∃ f : X → Y, IsBorelMeasurable f ∧ IsReduction f E F

theorem cosetRelation_equivalence (H : Submodule ℝ RealL2) :
    Equivalence (CosetRelation H) := by
  constructor
  · intro x
    simpa [CosetRelation] using H.zero_mem
  · intro x y h
    simpa [CosetRelation, neg_sub] using H.neg_mem h
  · intro x y z hxy hyz
    simpa [CosetRelation, sub_add_sub_cancel] using H.add_mem hxy hyz

theorem isBorelMeasurable_isBaireMeasurable {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsBorelMeasurable f) : IsBaireMeasurable f := by
  letI : MeasurableSpace X := borel X
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace X := ⟨rfl⟩
  letI : BorelSpace Y := ⟨rfl⟩
  intro U hU
  exact (hf hU.measurableSet).baireMeasurableSet

end NoUniversalFSigma


