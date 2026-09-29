-- Prove2me | Definitions.Def_Geometry_PosetTheory_SurrealTopology
-- name    : Geometry_PosetTheory_SurrealTopology
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:50.575344+00:00
-- url     : https://prove2.me/theorems/a4fe13fd-08cb-4eef-805c-02d6f9ead1fb
-- title:
--   Aether Catalog definitions — Geometry_PosetTheory_SurrealTopology
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PosetTheory.SurrealTopology`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PosetTheory/SurrealTopology.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Foundational Topological Theory of Surreal-Like Ordered Spaces

This module develops the theory of **cofinality spectra** for linearly ordered
topological spaces, establishing that uncountable cofinality is the precise
order-theoretic obstruction to first-countability in the order topology.

## Main Definitions

* `SurrealTopology.HasCountableLeftCof` — a point x has countable left
  cofinality if there is a sequence cofinal below x
* `SurrealTopology.HasCountableRightCof` — dual notion for right cofinality
* `SurrealTopology.OrderGap` — a Dedekind cut (L, R) with no realizing element
* `SurrealTopology.CofinalityClass` — classification of points as tame or wild

## Main Results

* `SurrealTopology.orderGap_clopen_lower` — the lower set of an order gap is clopen
* `SurrealTopology.orderGap_not_preconnected` — order gaps obstruct connectedness
* `SurrealTopology.first_countable_implies_tame` — first-countability forces
  countable cofinality from both sides
* `SurrealTopology.tame_implies_countably_generated_nhds` — countable cofinality
  from both sides yields countably generated neighborhood filter

## Mathematical Context

In surreal-like ordered spaces, many points have uncountable cofinality: no
countable sequence converges to them from below. This module shows this single
order-theoretic property is responsible for all topological pathology.
The **cofinality spectrum** partitions any linearly ordered space into "tame"
(behaving like ℝ) and "wild" (exhibiting surreal pathology) points.
-/

open Set Filter Topology

namespace SurrealTopology

variable {α : Type*}

/-! ## Cofinality Definitions -/

/-- A point `x` has **countable left cofinality** if there exists a sequence
`S : ℕ → α` cofinal in `Iio x`. The hypothesis guard ensures this is
only a nontrivial condition when `Iio x` is nonempty. -/
def HasCountableLeftCof [Preorder α] (x : α) : Prop :=
  (∃ a, a < x) →
  ∃ S : ℕ → α, (∀ n, S n < x) ∧ ∀ y, y < x → ∃ n, y ≤ S n

/-- A point `x` has **countable right cofinality** if there exists a sequence
coinitial in `Ioi x`. -/
def HasCountableRightCof [Preorder α] (x : α) : Prop :=
  (∃ b, x < b) →
  ∃ S : ℕ → α, (∀ n, x < S n) ∧ ∀ y, x < y → ∃ n, S n ≤ y

/-- A point is **tame** if it has countable cofinality from both sides. -/
def IsTame [Preorder α] (x : α) : Prop :=
  HasCountableLeftCof x ∧ HasCountableRightCof x

/-- A point is **wild** if it lacks countable cofinality from at least one side. -/
def IsWild [Preorder α] (x : α) : Prop := ¬IsTame x

/-! ## Order Gaps -/

/-- An **order gap** is an initial segment with no maximum whose complement
has no minimum — a "hole" in the order, like a Dedekind cut with no fill. -/
structure OrderGap (α : Type*) [LinearOrder α] where
  lower : Set α
  lower_nonempty : lower.Nonempty
  upper_nonempty : lowerᶜ.Nonempty
  lower_initial : ∀ x y, x ∈ lower → y ≤ x → y ∈ lower
  lower_lt_upper : ∀ x ∈ lower, ∀ y ∈ lowerᶜ, x < y
  no_max : ∀ x ∈ lower, ∃ y ∈ lower, x < y
  no_min : ∀ x ∈ lowerᶜ, ∃ y ∈ lowerᶜ, y < x

/-! ## Cofinality Spectrum Classification -/

/-- Classification of a point by its cofinality type. -/
inductive CofinalityClass where
  | tame      -- countable cofinality from both sides
  | wildLeft  -- uncountable from below
  | wildRight -- uncountable from above
  | wildBoth  -- uncountable from both sides
  deriving DecidableEq, Repr

/-- The tame locus of a linear order: all points with countable cofinality. -/
def tameLocus [Preorder α] : Set α := {x | IsTame x}

/-- The wild locus: complement of tame locus. -/
def wildLocus [Preorder α] : Set α := {x | IsWild x}

/-! ## Basic Cofinality Properties -/

section BasicCof

variable [LinearOrder α]



/-
If there is a predecessor element covering x, then x has countable left cofinality.
-/

end BasicCof

/-! ## Order Gap Topology -/

section GapTopology

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-
The lower set of an order gap is open: since it has no maximum,
every point has room above it within the lower set.
-/

/-
The upper set (complement of lower) of an order gap is open:
since it has no minimum, every point has room below it within the upper set.
-/


/-
**Order Gap Disconnection Theorem**: A linearly ordered topological space
with an order gap cannot be preconnected. The gap provides a nontrivial
clopen partition, which is the topological signature of disconnectedness.

This result establishes that order-completeness (Dedekind completeness)
is necessary for connectedness in ordered spaces.
-/

/-
A connected ordered space has no gaps.
-/

end GapTopology

/-! ## Wild Points and Countable Intersections -/

section WildPoints

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-
**Key Lemma**: In the order topology, any open neighborhood of a non-minimal
point `x` contains an open interval reaching below `x`.
-/

/-
**Countable Intersection for Uncountable Left Cofinality**: If `x` has
uncountable left cofinality, any countable family of neighborhoods shares
a common left-interval. This is the P-filter property from the left.

The proof: each neighborhood contains an interval (aₙ, x). Since `{aₙ}`
is countable and not cofinal below x, all aₙ are bounded by some b < x.
Then (b, x) lies in every neighborhood.
-/

/-
**First-countability forces countable left cofinality.** In the order
topology, if nhds x is countably generated, then x must have countable
left cofinality.
-/

/-
First-countability forces countable right cofinality (dual).
-/


end WildPoints

/-! ## Tame Points Have Countable Neighborhood Bases -/

section TameNhds

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-
**Tame implies countably generated nhds**: If x has countable left and
right cofinality (given explicitly as sequences), the open intervals
between approximants form a countable sub-basis for nhds x.
-/

end TameNhds

/-! ## Surreal-Like Spaces -/

section SurrealLike

/-- A **surreal-like space** is a linearly ordered topological space where
every non-extremal point is wild (has uncountable cofinality from at
least one side). This captures the essential character of the surreal numbers. -/
class SurrealLikeSpace (α : Type*) [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] : Prop where
  everywhere_wild : ∀ x : α, (∃ a, a < x) → (∃ b, x < b) → IsWild x

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]


end SurrealLike

/-! ## Partition Theorem -/

section Partition

variable [LinearOrder α]



end Partition

/-! ## Falsifiable Conjecture

**Conjecture (Tame Locus Openness)**: In a linearly ordered topological space
with the order topology, the tame locus is open.

**Computational test**: In ω₁ + 1, the tame locus is [0, ω₁) which is open.
In ω₁ · 2, points of countable cofinality form ω₁ ∪ [ω₁, ω₁·2), also open.
A counterexample would need a tame point every neighborhood of which
contains a wild point. -/

end SurrealTopology


