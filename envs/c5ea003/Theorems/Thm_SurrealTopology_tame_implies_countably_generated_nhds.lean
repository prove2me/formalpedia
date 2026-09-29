-- Prove2me | Theorems.Thm_SurrealTopology_tame_implies_countably_generated_nhds
-- name    : SurrealTopology.tame_implies_countably_generated_nhds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:53.856076+00:00
-- url     : https://prove2.me/theorems/fde374b9-21bc-4fcd-9c83-2641eaefaf4d
-- title:
--   Tame implies countably generated nhds
-- statement:
--   Formal statement of `SurrealTopology.tame_implies_countably_generated_nhds` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SurrealTopology.tame_implies_countably_generated_nhds    {x : α}
--       (hL : ∃ S : ℕ → α, (∀ n, S n < x) ∧ ∀ y, y < x → ∃ n, y ≤ S n)
--       (hR : ∃ S : ℕ → α, (∀ n, x < S n) ∧ ∀ y, x < y → ∃ n, S n ≤ y) :
--       (nhds x).IsCountablyGenerated := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PosetTheory/SurrealTopology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PosetTheory/SurrealTopology.lean#L292

-- Thm stub generated from Geometry/PosetTheory/SurrealTopology.lean
import Mathlib
import Definitions.Def_Geometry_PosetTheory_SurrealTopology
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

open SurrealTopology

variable {α : Type*}

/-! ## Cofinality Definitions -/





/-! ## Order Gaps -/


/-! ## Cofinality Spectrum Classification -/




/-! ## Basic Cofinality Properties -/


variable [LinearOrder α]



/-
If there is a predecessor element covering x, then x has countable left cofinality.
-/


/-! ## Order Gap Topology -/


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


/-! ## Wild Points and Countable Intersections -/


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



/-! ## Tame Points Have Countable Neighborhood Bases -/


variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-
**Tame implies countably generated nhds**: If x has countable left and
right cofinality (given explicitly as sequences), the open intervals
between approximants form a countable sub-basis for nhds x.
-/

theorem SurrealTopology.tame_implies_countably_generated_nhds    {x : α}
    (hL : ∃ S : ℕ → α, (∀ n, S n < x) ∧ ∀ y, y < x → ∃ n, y ≤ S n)
    (hR : ∃ S : ℕ → α, (∀ n, x < S n) ∧ ∀ y, x < y → ∃ n, S n ≤ y) :
    (nhds x).IsCountablyGenerated := by sorry
