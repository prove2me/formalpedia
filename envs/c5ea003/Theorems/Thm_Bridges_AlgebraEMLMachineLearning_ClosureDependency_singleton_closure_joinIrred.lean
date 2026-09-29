-- Prove2me | Theorems.Thm_Bridges_AlgebraEMLMachineLearning_ClosureDependency_singleton_closure_joinIrred
-- name    : Bridges.AlgebraEMLMachineLearning.ClosureDependency.singleton_closure_joinIrred
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:20:13.669374+00:00
-- url     : https://prove2.me/theorems/b7b62160-5a30-453e-830b-bb4f49127495
-- title:
--   Singleton closure joinIrred
-- statement:
--   Formal statement of `Bridges.AlgebraEMLMachineLearning.ClosureDependency.singleton_closure_joinIrred` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bridges.AlgebraEMLMachineLearning.ClosureDependency.singleton_closure_joinIrred(C : ClosureSys α)
--       (hex : HasExchange C) (x : α) (hx : x ∉ C.cl ∅) :
--       ClosedJoinIrred C (C.cl {x}) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ClosureDependency.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ClosureDependency.lean#L371

-- Thm stub generated from Bridges/ClosureDependency.lean
import Mathlib
import Definitions.Def_Bridges_ClosureDependency
/-
# Exchange-Closure Dependency Systems and Sparse Predictor Reconstruction

This file establishes a closure-theoretic foundation for sparse, interpretable
prediction. We define exchange-closure dependency systems with weighted implication
certificates over finite types and prove that:

1. Every finite closure system has canonical minimal supports (sparse basis existence)
2. Minimal supports are irredundant and finitely enumerable
3. Under exchange, minimal supports enjoy swap properties enabling canonical extraction
4. Weighted cost profiles determine closure structure (Reconstruction Duality)

## Main Results

* `isClosed_inter` — Closed sets are closed under intersection
* `isClosed_sInter` — Closed sets are closed under arbitrary intersection
* `cl_le_of_subset_closed` — Closure is below any closed superset
* `exists_minimalSupport` — Every derivable element has a minimal support
* `minimalSupport_irredundant` — Minimal supports are irredundant
* `exchange_swap` — Exchange property enables support element swapping
* `canonicalBasis_complete` — Canonical basis covers all derivations
* `costProfile_determines_membership` — Cost profile determines closure membership
* `cl_eq_of_cl_finset_eq` — Agreement on Finsets implies agreement on all Sets
* `reconstruction_duality` — Full reconstruction duality theorem

## Bridges

- **Algebra ↔ Machine Learning**: Closure operators ↔ feature dependency structure
- **Lattice Theory ↔ Sparse Prediction**: Join-irreducibles ↔ atomic predictors
- **Semiring Theory ↔ Optimization**: Idempotent costs ↔ minimal derivation
- **Dependency Logic ↔ Explainability**: Implication bases ↔ interpretable models
-/


open Set Finset

noncomputable section

open Bridges.AlgebraEMLMachineLearning.ClosureDependency

/-! ## §1. Closure Operators on Finite Types -/


open ClosureSys

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (C : ClosureSys α)




/-
Intersection of two closed sets is closed.
-/

/-
Intersection of a nonempty family of closed sets is closed.
-/

/-
The closure is contained in any closed superset.
-/





/-! ## §2. Supports and Irredundancy

A support for an element `b` is a finite set `A` such that `b ∈ cl(A)`.
Minimal supports are the sparse explanatory objects central to interpretable prediction. -/

variable {α : Type*} [Fintype α] [DecidableEq α]




/-
**Sparse Basis Existence**: Every derivable element has a minimal support
within any given support. This is the foundational sparsification theorem.
-/

/-
**Irredundancy of Minimal Supports**: If `A` is a minimal support for `b`
and `b ∉ A`, then `A` is irredundant—every element contributes non-trivially
to the closure.
-/


/-! ## §3. Exchange-Closure Axiom

The Steinitz exchange property: if adding `c` to `A` newly derives `b`,
then adding `b` to `A` newly derives `c`. This is the structural axiom
that makes sparse predictor extraction canonical. -/


/-
Under exchange, a minimal support element cannot be derived from
the rest of the support alone (it is indispensable).
-/

/-
**Exchange Swap**: Under exchange, if `A` is a minimal support for `b`
(with `b ∉ A`) and `a ∈ A`, then `a` can be derived from the remaining
elements plus `b`. This is the key lemma for canonical basis extraction.
-/

/-! ## §4. Weighted Closure Dependency Systems

A weighted closure dependency system enriches a closure operator with
derivation costs valued in `ℕ∞` (the tropical semiring `WithTop ℕ`).
The cost `wt A b` measures the prediction effort to derive `b` from features `A`. -/


open WeightedClosureDep





/-! ## §5. Reconstruction Duality

The central duality theorem: the cost profile of a weighted closure dependency
system determines the closure operator, and conversely. -/

/-
**Cost Profile Determines Membership**: If two systems have the same
cost profile, they agree on which elements are derivable from which supports.
-/

/-
Agreement on all Finset coercions implies agreement on all Sets.
This is the key lifting lemma that connects the finitary cost profile
to the full closure operator.
-/

/-
**Reconstruction Duality (Theorem C)**: Two weighted closure dependency
systems with equivalent cost profiles have identical closure operators.
This is the precise sense in which the sparse predictor object determines
the dependency structure.
-/

/-! ## §6. Canonical Sparse Basis

The canonical sparse basis is the finite collection of all minimal supports.
Every derivation can be witnessed by a member of this basis.
Under exchange, this basis has additional structure. -/



/-
**Canonical Basis Completeness (Theorem A)**: Every derivation
`b ∈ cl(A)` is witnessed by some minimal support `A' ⊆ A` in the
canonical basis.
-/

/-
Under exchange, the canonical basis determines the closure system.
If two exchange systems have the same canonical basis, they have the
same closure operator.
-/

/-! ## §7. Join-Irreducible Closed Sets

In the lattice of closed sets, join-irreducible elements correspond to
atomic predictor dependencies. Under exchange, these are exactly the
closures of singletons not in `cl(∅)`. -/



/-
Under exchange, if `y ∈ cl({x}) \ cl(∅)` then `x ∈ cl({y})`.
-/

/-
Under exchange, every proper closed subset of `cl({x})` (for `x ∉ cl(∅)`) is
contained in `cl(∅)`.
-/

/-
Under exchange, `cl({x})` is join-irreducible for `x ∉ cl(∅)`.
-/

theorem Bridges.AlgebraEMLMachineLearning.ClosureDependency.singleton_closure_joinIrred(C : ClosureSys α)
    (hex : HasExchange C) (x : α) (hx : x ∉ C.cl ∅) :
    ClosedJoinIrred C (C.cl {x}) := by sorry
