-- Prove2me | Definitions.Def_Bridges_SurrealTopologyDeep
-- name    : Bridges_SurrealTopologyDeep
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:25.608692+00:00
-- url     : https://prove2.me/theorems/c9b3f3d8-4b6d-49fd-b1fa-97485021d084
-- title:
--   Aether Catalog definitions — Bridges_SurrealTopologyDeep
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SurrealTopologyDeep`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SurrealTopologyDeep.lean by skeleton subtraction
import Mathlib

set_option autoImplicit false

open Set TopologicalSpace Filter

/-! # Surreal Topology: Deep Structure of Ordered Continua

This file develops the deep structural theory connecting order-theoretic gap structure
to topological properties of linearly ordered spaces. We establish:

1. **Order Gap Theory**: Dedekind gaps and their relationship to connectedness.
2. **Cofinality-Topology Duality**: Order-theoretic cofinality ↔ first-countability.
3. **Archimedean Characterization**: Equivalence of Archimedean property with
   boundedness by naturals.
4. **Compactness Obstructions**: Non-compactness from unboundedness.

## Novel Definitions

* `OrderGap` — a Dedekind gap (cut with no realizing element).
* `GapFree` — the order has no gaps.
* `HasCountableLocalBasis` — countable local basis at a point.

## Catalog References

* `Catalog/Bridges/SurrealTopology.lean`
* `Catalog/Catalog/Bridges/SurrealTopologyExtended.lean`
-/

/-! ## Part I: Order Gap Theory -/

/-- An **order gap** (Dedekind gap) in a linear order is a partition into
a nonempty lower set `L` and nonempty upper set `R` where `L` has no maximum
and `R` has no minimum. This is the order-theoretic obstruction to connectedness. -/
structure OrderGap (α : Type*) [LinearOrder α] where
  lower : Set α
  upper : Set α
  lower_nonempty : lower.Nonempty
  upper_nonempty : upper.Nonempty
  partition : lower ∪ upper = univ
  disjoint : Disjoint lower upper
  lower_downward : ∀ ⦃a b : α⦄, a ≤ b → b ∈ lower → a ∈ lower
  upper_upward : ∀ ⦃a b : α⦄, a ≤ b → a ∈ upper → b ∈ upper
  lower_no_max : ∀ a : α, a ∈ lower → ∃ b : α, b ∈ lower ∧ a < b
  upper_no_min : ∀ a : α, a ∈ upper → ∃ b : α, b ∈ upper ∧ b < a

/-- A linear order is **gap-free** if no `OrderGap` exists. -/
def GapFree (α : Type*) [LinearOrder α] : Prop :=
  IsEmpty (OrderGap α)

/-! ## Part II: Conditionally Complete Orders are Gap-Free -/

/-
**A conditionally complete linear order has no Dedekind gaps.**

*Proof*: Given a gap (L, R), L is nonempty and bounded above (by elements of R).
Let s = sSup L. Either s ∈ L (contradicting no-max) or s ∈ R (contradicting no-min
via the upper bound property).
-/

/-! ## Part III: Gaps ↔ Topology -/

/-
**The lower set of a gap is open in the order topology.**
For any a ∈ L, find b ∈ L with a < b; then Iio b ⊆ L (by downward closure)
and is an open neighborhood of a.
-/

/-
**The upper set of a gap is open in the order topology.**
-/

/-
**A connected linear order with order topology is gap-free.**
A gap produces two nonempty disjoint open sets covering the space,
contradicting connectedness.
-/

/-! ## Part IV: Cofinality Sequences -/

/-
**A countable nonempty coinitial set above x yields a coinitial sequence.**
Uses the fact that countable nonempty sets can be enumerated as a range.
-/

/-! ## Part V: Order Isomorphisms are Homeomorphisms -/

/-
**Every order isomorphism between ordered topological spaces is continuous.**
-/

/-
**The inverse of an order isomorphism is continuous.**
-/

/-! ## Part VI: Dense Order Separation -/

/-
**In a densely ordered space, distinct points have an intermediate separator.**
This gives an explicit Hausdorff separation construction.
-/

/-! ## Part VII: Archimedean Characterization -/

/-
**A positive element in an Archimedean ordered additive commutative monoid
is bounded above by some natural multiple of any positive element.**
Restated: the Archimedean property gives ∃ n, x ≤ n • y for any x and positive y.
-/

/-! ## Part VIII: Compactness Obstructions -/

/-
**A nonempty ordered space with no minimum is not compact.**
Dual of the no-maximum case. Cover by {Ioi a | a : α}.
-/

/-
**An infinite discrete space is noncompact.**
-/

/-! ## Part IX: Connected Image -/

/-
**The image of a connected set under a continuous map is connected.**
-/

/-! ## Part X: Countable Local Basis -/

/-- A point has a **countable local basis** if there exists a countable family
of open neighborhoods forming a basis of the neighborhood filter. -/
def HasCountableLocalBasis {α : Type*} [TopologicalSpace α] (x : α) : Prop :=
  ∃ (B : ℕ → Set α), (∀ n : ℕ, IsOpen (B n)) ∧ (∀ n : ℕ, x ∈ B n) ∧
    ∀ U : Set α, U ∈ nhds x → ∃ n : ℕ, B n ⊆ U

/-
**Every point in ℝ has a countable local basis.**
-/

/-
**Every point in a second-countable space has a countable local basis.**
-/

/-! ## Part XI: Disconnectedness Results -/

/-
**ℚ is not connected.**
The sets {q ∈ ℚ | q < √2} and {q ∈ ℚ | q > √2} disconnect ℚ.
-/

/-
**ℤ is not connected.**
-/


/-! ## Falsifiable Conjecture

**Conjecture (Gap-Completeness Duality):**
For a linear order `α` with no endpoints and order topology:
`α` is connected ↔ `α` is gap-free AND conditionally complete.

**Testable Predictions:**
- ℚ: gap-free ✓, not conditionally complete ✓, not connected ✓
- ℝ: gap-free ✓, conditionally complete ✓, connected ✓
- ℤ: has gaps ✗, not connected ✓

**Potential counterexample:** Suslin lines (independent of ZFC).
-/


