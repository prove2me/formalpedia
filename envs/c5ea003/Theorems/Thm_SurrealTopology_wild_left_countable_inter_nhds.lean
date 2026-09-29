-- Prove2me | Theorems.Thm_SurrealTopology_wild_left_countable_inter_nhds
-- name    : SurrealTopology.wild_left_countable_inter_nhds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:53:19.142187+00:00
-- url     : https://prove2.me/theorems/4a6ec949-abdd-4e7f-b6c3-70108b4d6120
-- title:
--   Wild left countable inter nhds
-- statement:
--   Formal statement of `SurrealTopology.wild_left_countable_inter_nhds` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SurrealTopology.wild_left_countable_inter_nhds    {x : α} (hx : ¬HasCountableLeftCof x)
--       {U : ℕ → Set α} (hU : ∀ n, U n ∈ nhds x) :
--       ∃ b, b < x ∧ ∀ z, b < z → z < x → ∀ n, z ∈ U n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PosetTheory/SurrealTopology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PosetTheory/SurrealTopology.lean#L203

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

theorem SurrealTopology.wild_left_countable_inter_nhds    {x : α} (hx : ¬HasCountableLeftCof x)
    {U : ℕ → Set α} (hU : ∀ n, U n ∈ nhds x) :
    ∃ b, b < x ∧ ∀ z, b < z → z < x → ∀ n, z ∈ U n := by sorry
