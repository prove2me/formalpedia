-- Prove2me | Definitions.Def_Bridges_PosetTheory_SurrealTopologyExtended
-- name    : Bridges_PosetTheory_SurrealTopologyExtended
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:49.635+00:00
-- url     : https://prove2.me/theorems/59bed016-ab24-495a-aa8e-dfa05461bb3d
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_SurrealTopologyExtended
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.SurrealTopologyExtended`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/SurrealTopologyExtended.lean by skeleton subtraction
import Mathlib

open Set TopologicalSpace Filter

/-! # Surreal Topology: Open Sets at Infinity

This file extends the topological theory of ordered continua motivated by Conway's
surreal numbers. We prove:

1. **Unbounded ordered topological spaces are noncompact** via explicit open covers.
2. **Uncountable coinitiality obstructs countable bases** above a point.
3. **Open set extension via order embeddings** is always open.
4. **Hausdorff, connectedness, and separation** results for order topologies.
5. **Order-convex sets** are closed under intersections and monotone preimages.

## Novel Definitions

* `UncountableUpperCoinitiality` — captures the coinitiality gap structure at a point,
  abstracting the key property that makes surreal numbers topologically exotic.
* `SurrealOpenExtension` — canonical extension of an open set from a sub-order
  to the ambient order via an order embedding.

## References

* J.H. Conway, *On Numbers and Games*, Academic Press, 1976.
* P. Ehrlich, *Bulletin of Symbolic Logic*, 2012.
-/

/-! ## Novel Definitions -/

/-- A point `x` has *uncountable upper coinitiality* if no countable subset of `{y | x < y}`
is coinitial — for every countable `S ⊆ {y | x < y}`, there exists `z` with
`x < z` such that no element of `S` is `≤ z`. This abstracts the key feature of surreal
numbers: between any surreal and the elements above it lies a gap that cannot be bridged
by any sequence. -/
def UncountableUpperCoinitiality {α : Type*} [Preorder α] (x : α) : Prop :=
  ¬ ∃ (S : Set α), S.Countable ∧ (∀ s ∈ S, x < s) ∧
    (∀ y, x < y → ∃ s ∈ S, s ≤ y)


/-- The surreal extension of an open set: given an order embedding `f : α ↪o β`,
the surreal extension of `U ⊆ α` is the union of all open intervals `(f(a), f(b))`
where `a < b` and `Ioo a b ⊆ U`. -/
def SurrealOpenExtension {α β : Type*} [Preorder α] [Preorder β]
    [TopologicalSpace β] [OrderTopology β]
    (f : α ↪o β) (U : Set α) : Set β :=
  ⋃ (a : α) (b : α) (_ : a < b) (_ : Ioo a b ⊆ U), Ioo (f a) (f b)

/-- A set `s` in an ordered type is *order-convex* if whenever `a, b ∈ s` and
`a ≤ c ≤ b`, then `c ∈ s`. (Local definition to avoid import dependency.) -/
def IsOrderConvex' {α : Type*} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b c : α⦄, a ∈ s → b ∈ s → a ≤ c → c ≤ b → c ∈ s

/-! ## Theorem 1: Finite Initial-Segment Covers Fail for Unbounded Orders -/



/-! ## Theorem 2: Uncountable Coinitiality Obstructs Countable Bases -/



/-! ## Theorem 3: Open Set Extension is Open -/



/-! ## Theorem 4: Hausdorff and Separation -/

/-- **The order topology on any linear order is T₂ (Hausdorff).** -/
instance orderTopology_t2 (α : Type*) [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] : T2Space α :=
  inferInstance


/-! ## Theorem 5: Connectedness -/


/-! ## Theorem 6: Order-Convex Sets Under Intersections and Preimages -/




/-! ## Theorem 7: Surreal Extension Monotonicity -/



/-! ## Theorem 8: Real Numbers Exemplify Non-compact Connected Order -/



/-! ## Falsifiable Conjecture

**Conjecture (Countable Coinitiality ↔ Separability for Linear Orders):**
In any linearly ordered topological space with order topology, if every point has
both countable upper coinitiality and countable lower cofinality, then the space
is separable (has a countable dense subset).

**Computational Test:**
- ℚ: countable coinitiality everywhere, separable. ✓
- ℝ: countable coinitiality (via ℚ), separable. ✓
- ω₁: some points have uncountable coinitiality, not separable. Consistent. ✓

**Potential Counterexample:** A Suslin line (ccc but not separable) would be a
counterexample. The existence of Suslin lines is independent of ZFC, making this
conjecture potentially undecidable! This connection between order-theoretic gap
structure and topological weight is genuinely open.

**Testable Prediction:** For any countable dense linear order with no endpoints,
separability holds trivially (the order itself is countable hence dense in itself).
-/


