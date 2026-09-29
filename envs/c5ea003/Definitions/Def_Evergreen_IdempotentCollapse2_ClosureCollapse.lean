-- Prove2me | Definitions.Def_Evergreen_IdempotentCollapse2_ClosureCollapse
-- name    : Evergreen_IdempotentCollapse2_ClosureCollapse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:22.86946+00:00
-- url     : https://prove2.me/theorems/934e7d8e-719c-4003-b8fa-93b5ad06e3ff
-- title:
--   Aether Catalog definitions — Evergreen_IdempotentCollapse2_ClosureCollapse
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.IdempotentCollapse2.ClosureCollapse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/IdempotentCollapse2/ClosureCollapse.lean by skeleton subtraction
import Mathlib

/-!
# Direction 5: Closure Operators — The Algebraic Side of Collapse

## The Insight

A **closure operator** on a partially ordered set is a function c that is:
1. Extensive: x ≤ c(x) — closure never shrinks
2. Monotone: x ≤ y → c(x) ≤ c(y) — order-preserving
3. **Idempotent**: c(c(x)) = c(x) — closing twice = closing once

Examples: topological closure, convex hull, span, generated ideal, transitive closure.

## Main Results

* `topological_closure_idempotent` — cl(cl(A)) = cl(A)
* `interior_idempotent` — interior ∘ interior = interior
* `convex_hull_idempotent` — conv(conv(S)) = conv(S)
* `span_idempotent` — Submodule.span is idempotent
* `ClosureOp.cl_is_closed` — Every closure value is closed
* `ClosureOp.closed_eq_range` — Closed elements = range of closure
* `galois_closure_idempotent` — Galois connections give closures
* `transitive_closure_idempotent` — tc(tc(R)) = tc(R)
-/

open Set

variable {α : Type*}

/-! ### Topological Closure is Idempotent -/



/-! ### Convex Hull is Idempotent -/

/-
PROBLEM
The convex hull is idempotent.

PROVIDED SOLUTION
The convex hull of a convex set is itself. convexHull ℝ S is convex, so convexHull ℝ (convexHull ℝ S) = convexHull ℝ S. Use that convex_convexHull or (convexHull ℝ S).convexHull_eq or similar.
-/

/-! ### Linear Span is Idempotent -/

/-
PROBLEM
Submodule span is idempotent.

PROVIDED SOLUTION
Submodule.span of a submodule is itself. Use Submodule.span_eq for the submodule (Submodule.span R S).
-/

/-! ### Abstract Closure Operators -/

/-- An abstract closure operator on a partial order. -/
structure ClosureOp (α : Type*) [Preorder α] where
  cl : α → α
  extensive : ∀ x, x ≤ cl x
  monotone : ∀ x y, x ≤ y → cl x ≤ cl y
  idempotent : ∀ x, cl (cl x) = cl x

/-- The closed elements are exactly the fixed points. -/
def ClosureOp.Closed {α : Type*} [Preorder α] (c : ClosureOp α) (x : α) : Prop :=
  c.cl x = x




/-! ### Galois Connections Yield Closure Operators -/


/-! ### Composing Closures -/

/-
PROBLEM
Composing two closure operators (when they commute) gives an idempotent.

PROVIDED SOLUTION
(c₁ ∘ c₂)(c₁(c₂(x))) = c₁(c₂(c₁(c₂(x)))) = c₁(c₁(c₂(c₂(x)))) by h_comm = c₁(c₂(c₂(x))) by c₁.idempotent = c₁(c₂(x)) by c₂.idempotent.
-/

/-! ### Transitive Closure as Idempotent Collapse -/


