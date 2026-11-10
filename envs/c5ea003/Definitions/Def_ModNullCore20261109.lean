-- Prove2me | Definitions.Def_ModNullCore20261109
-- name    : ModNullCore20261109
-- status  : Definition
-- author  : @username
-- created : 2026-11-09T09:00:16.224686+00:00
-- url     : https://prove2.me/theorems/f9034766-9c1a-47a1-a99b-84b4c49e97dc
-- title:
--   Borel complexity, reductions, and well-founded tree indices
-- statement:
--   The bundle defines $F_\sigma$ and $K_\sigma$ sets by countable unions of closed and compact sets. It defines $\Sigma^0_3$ by countable unions of $G_\delta$ sets and $\Pi^0_3$ by countable intersections of $F_\sigma$ sets, with $\Delta^0_3$ their intersection. The separate difference-of-two-$F_\sigma$ predicate is a stronger refinement, not a definition of all $\Delta^0_3$ sets.
--
--   A Borel reduction is a measurable map preserving and reflecting the relation for every pair. A standard Borel equivalence bundles its carrier, actual measurable structure, standard-Borel property, equivalence laws, and measurable graph; empty target spaces are permitted. Tree codes are prefix-closed Boolean functions on finite natural-number lists. The index type consists of those codes admitting no infinite natural-number branch; the empty tree is included, and the index type is not asserted countable. The bundle also defines invariant domains and the bounded-difference relation on real sequences.
-- source:
--   Universality modulo null sets in the Borel hierarchy, user-supplied unpublished manuscript dated 9 November 2026; SHA-256 48745c75427f83370292c2e4cf91ec06377e80472252db0182599edcd05e2d97, Sections 2 and 5; the bounded-difference benchmark is specified in Section 6.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.GDelta.Basic
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace ModNullUniversality

def IsFSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ s = ⋃ n, C n

def IsKSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsCompact (C n)) ∧ s = ⋃ n, C n

def IsSigma3 {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsGδ (C n)) ∧ s = ⋃ n, C n

def IsPi3 {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsFSigma (C n)) ∧ s = ⋂ n, C n

def IsDelta3 {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  IsSigma3 s ∧ IsPi3 s

def DifferenceFSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ A B : Set X, IsFSigma A ∧ IsFSigma B ∧ s = A \ B

def BorelReducible {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x y, E x y ↔ F (f x) (f y)

structure StandardBorelEquivalence where
  Carrier : Type
  [measurable : MeasurableSpace Carrier]
  [standard : StandardBorelSpace Carrier]
  rel : Carrier → Carrier → Prop
  equivalence : Equivalence rel
  measurable_graph : MeasurableSet {p : Carrier × Carrier | rel p.1 p.2}

attribute [instance] StandardBorelEquivalence.measurable StandardBorelEquivalence.standard

abbrev Node := List ℕ

def PrefixClosed (T : Node → Bool) : Prop :=
  ∀ s n, T (s ++ [n]) = true → T s = true

def TreeSpace := {T : Node → Bool // PrefixClosed T}

def HasBranch (T : TreeSpace) : Prop :=
  ∃ b : ℕ → ℕ, ∀ n, T.val (List.ofFn (fun i : Fin n => b i)) = true

def WF := {T : TreeSpace // ¬ HasBranch T}

def IsInvariant {X : Type*} (E : X → X → Prop) (C : Set X) : Prop :=
  ∀ x y, E x y → (x ∈ C ↔ y ∈ C)

def LInfinityRelation (x y : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n, |x n - y n| ≤ M

end ModNullUniversality


