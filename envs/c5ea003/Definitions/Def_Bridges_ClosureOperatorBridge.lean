-- Prove2me | Definitions.Def_Bridges_ClosureOperatorBridge
-- name    : Bridges_ClosureOperatorBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:36.463742+00:00
-- url     : https://prove2.me/theorems/c33384d9-04f1-47e3-9516-5260754235e8
-- title:
--   Aether Catalog definitions — Bridges_ClosureOperatorBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureOperatorBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureOperatorBridge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Fixed-Point Lattice Theorem for Idempotent Monotone Bridge Operators

This file establishes the universal bridge mechanism connecting tropical algebra,
lattice theory, automata minimization, and semantic normalization through a single
structural theorem: **idempotent monotone inflationary operators are exactly closure
operators**, and their fixed-point sets inherit rich order-theoretic structure.

## Main results

* `bridgeClosureOperator` — constructs a `ClosureOperator` from monotone + inflationary
  + idempotent hypotheses
* `range_eq_fixedPoints_of_idempotent` — the range of any idempotent equals its
  fixed-point set (generalization of `master_equation_general`)
* `isLeast_fixedPoint_above` — `O x` is the least fixed point above `x`
* `fixedPoints_closed_under_sInf` — fixed points of a closure operator on a complete
  lattice are closed under arbitrary infima
* `fixedPoints_completeLattice` — the fixed-point set inherits complete lattice structure
* `idempotent_sup_inf_structure` — commuting idempotents in a commutative ring form a
  lattice under `e*f` (meet) and `e+f-e*f` (join)
* `idem_order_refl`, `idem_order_antisymm`, `idem_order_trans` — the idempotent order
  `e*f = e` is a partial order on commuting idempotents
* `fixedPoint_retract_of_idempotent_nonexpansive` — metric retraction theorem for
  idempotent nonexpansive maps

## Cross-domain significance

This theorem unifies:
- **Tropical projections** as closure operators on min-plus lattices
- **Semantic normalization** as fixed-point extraction
- **Automata minimization** as closure in the Nerode quotient lattice
- **Lattice relaxation** in post-quantum cryptography as closure saturation
- **Optimization** as least-fixed-point computation

## References

* Birkhoff, "Lattice Theory" (1967)
* Davey & Priestley, "Introduction to Lattices and Order" (2002)
* Mathlib `Order.Closure`
-/


namespace Bridges.ClosureOperatorBridge

open Set Function

/-! ## §1. The Bridge Closure Operator

The foundational construction: any monotone, inflationary, idempotent map
on a partial order is a closure operator in the precise lattice-theoretic sense.
-/

/-- **Bridge Closure Operator Construction.**
Given a function `O : α → α` on a partial order that is monotone, inflationary
(`x ≤ O x`), and idempotent (`O (O x) = O x`), we construct the canonical
`ClosureOperator` structure. This is the universal theorem explaining why
bridge constructions recur across algebra, order, dynamics, and semantics. -/
noncomputable def bridgeClosureOperator
    {α : Type*} [PartialOrder α] (O : α → α)
    (hmono : Monotone O)
    (hle : ∀ x, x ≤ O x)
    (hidem : ∀ x, O (O x) = O x) :
    ClosureOperator α :=
  ClosureOperator.mk' O hmono hle (fun x => le_of_eq (hidem x))


/-! ## §2. Range = Fixed Points (Order-Theoretic Master Equation)

The fundamental identity: for any idempotent, the range equals the fixed-point set.
This lifts `master_equation_general` into the order-theoretic setting.
-/


/-! ## §3. Least Fixed Point Above (The Decisive Structural Theorem)

This is the most conceptually important result: `O x` is not just *a* fixed point
above `x`, but the *least* such fixed point. This characterizes closure operators
uniquely and explains why bridge constructions produce canonical results.
-/



/-
**Least Fixed Point Above Theorem.**
For a monotone, inflationary, idempotent operator `O` on a preorder,
`O x` is the least element of `{y | x ≤ y ∧ O y = y}`.

This is the decisive structural theorem: it says that applying `O` to any element
produces the *canonical* closed element above it. In tropical geometry, this is
tropical projection. In semantics, this is normalization. In automata theory,
this is minimization.
-/

/-! ## §4. Fixed Points Closed Under Infima

In a complete lattice, the fixed-point set of a closure operator is closed
under arbitrary infima. This gives the fixed-point set its own complete
lattice structure.
-/

/-
**Fixed points are closed under infima.**
If `O` is monotone, inflationary, and idempotent on a complete lattice,
then the infimum of any set of fixed points is again a fixed point.

This is a key structural result: it means the fixed-point set is not just
a subset but a *complete sublattice* (for infima).
-/


/-! ## §5. IsClosed Predicate Properties -/



/-! ## §6. Monotone Idempotent Retraction on Fixed Points

The restriction of `O` to its range gives an order isomorphism between
the range (with the induced order) and the fixed-point set.
-/



/-! ## §7. Algebraic Idempotent Lattice Structure

Commuting idempotents in a commutative ring form a lattice under
the operations `e*f` (meet) and `e+f-e*f` (join). This bridges
ring theory, lattice theory, and projector semantics.
-/

/-
**Idempotent Meet is Idempotent.**
The product of two idempotents in a commutative ring is idempotent.
-/

/-
**Idempotent Join is Idempotent.**
The expression `e + f - e*f` of two idempotents in a commutative ring
is itself idempotent.
-/


/-! ## §8. Idempotent Order Structure

Define the natural partial order on idempotents: `e ≤ f` iff `e * f = e`.
-/

/-- The idempotent order: `e ≤ f` in the idempotent partial order iff `e * f = e`. -/
def IdemLE {R : Type*} [Mul R] (e f : R) : Prop := e * f = e

/-
The idempotent order is reflexive on idempotents.
-/

/-
The idempotent order is antisymmetric on elements of a commutative ring.
-/

/-
The idempotent order is transitive.
-/

/-
Meet (`e*f`) is below both `e` and `f` in the idempotent order.
-/

/-
Meet (`e*f`) is below both `e` and `f` in the idempotent order.
-/

/-
Join (`e+f-e*f`) is above both `e` and `f` in the idempotent order.
-/

/-
Join (`e+f-e*f`) is above both `e` and `f` in the idempotent order.
-/

/-! ## §9. Metric Retraction Theorem

An idempotent nonexpansive map on a metric space is a retraction onto
its fixed-point set.
-/



/-
**Fixed points of nonexpansive idempotent are metrically closed.**
If `P` is continuous (which follows from nonexpansiveness on metric spaces),
the fixed-point set `{x | P x = x}` is closed.
-/

/-! ## §10. Cross-Domain Instantiation: Real-Valued Closure

Demonstrate the theorem on a concrete example: `max 0` (ReLU) as a
closure operator on `ℝ` with the usual order.
-/

/-
ReLU (`max 0 x`) is monotone.
-/

/-
ReLU is inflationary.
-/

/-
ReLU is idempotent.
-/


/-
ReLU's fixed points are exactly the nonnegative reals.
-/


/-! ## §11. Closure Operator Composition

Two closure operators compose to a closure operator when they commute.
This models sequential application of bridge transformations.
-/

/-
Composition of commuting closure operators yields an inflationary
idempotent monotone map.
-/

/-
Composition of commuting closure operators is idempotent.
-/

end Bridges.ClosureOperatorBridge


