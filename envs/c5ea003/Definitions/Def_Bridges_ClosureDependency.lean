-- Prove2me | Definitions.Def_Bridges_ClosureDependency
-- name    : Bridges_ClosureDependency
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:54.056595+00:00
-- url     : https://prove2.me/theorems/fc1969e5-4091-4120-9832-4fca6aea8e09
-- title:
--   Aether Catalog definitions — Bridges_ClosureDependency
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureDependency`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureDependency.lean by skeleton subtraction
import Mathlib
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

namespace Bridges.AlgebraEMLMachineLearning.ClosureDependency

/-! ## §1. Closure Operators on Finite Types -/

/-- A closure operator on `Set α`: extensive, monotone, idempotent.
This is the foundational object for dependency geometry. -/
structure ClosureSys (α : Type*) where
  cl : Set α → Set α
  cl_extensive : ∀ S, S ⊆ cl S
  cl_monotone : ∀ ⦃S T⦄, S ⊆ T → cl S ⊆ cl T
  cl_idempotent : ∀ S, cl (cl S) = cl S

namespace ClosureSys

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (C : ClosureSys α)

/-- A set is closed if it equals its own closure. -/
def IsClosed (S : Set α) : Prop := C.cl S = S



/-
Intersection of two closed sets is closed.
-/

/-
Intersection of a nonempty family of closed sets is closed.
-/

/-
The closure is contained in any closed superset.
-/




end ClosureSys

/-! ## §2. Supports and Irredundancy

A support for an element `b` is a finite set `A` such that `b ∈ cl(A)`.
Minimal supports are the sparse explanatory objects central to interpretable prediction. -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `A` is a support for `b` under closure `C`: the feature set `A` determines `b`. -/
def IsSupport (C : ClosureSys α) (A : Finset α) (b : α) : Prop :=
  b ∈ C.cl (↑A)

/-- `A` is a minimal support for `b`: no proper subset suffices. -/
def IsMinimalSupport (C : ClosureSys α) (A : Finset α) (b : α) : Prop :=
  IsSupport C A b ∧ ∀ A' : Finset α, A' ⊂ A → ¬IsSupport C A' b

/-- `A` is irredundant: removing any single element changes the closure. -/
def IsIrredundantSupport (C : ClosureSys α) (A : Finset α) : Prop :=
  ∀ a ∈ A, C.cl (↑(A.erase a) : Set α) ≠ C.cl (↑A)

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

/-- A closure system has the exchange property (Steinitz–Mac Lane exchange). -/
def HasExchange (C : ClosureSys α) : Prop :=
  ∀ (A : Set α) (x y : α),
    y ∈ C.cl (A ∪ {x}) → y ∉ C.cl A → x ∈ C.cl (A ∪ {y})

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

/-- A weighted closure dependency system: a closure operator with costs.
The weight function `wt` assigns a cost to each derivation `(A, b)`,
with `wt A b < ⊤` iff `b ∈ cl(A)`. -/
structure WeightedClosureDep (α : Type*) [Fintype α] [DecidableEq α]
    extends ClosureSys α where
  wt : Finset α → α → ℕ∞
  wt_iff_mem_cl : ∀ (A : Finset α) (b : α), b ∈ cl ↑A ↔ wt A b < ⊤

namespace WeightedClosureDep

/-- The prediction cost of deriving `b` from support `A`. -/
def predCost (D : WeightedClosureDep α) (A : Finset α) (b : α) : ℕ∞ := D.wt A b

/-- Two weighted systems have equivalent cost profiles. -/
def CostProfileEquiv (D₁ D₂ : WeightedClosureDep α) : Prop :=
  ∀ (A : Finset α) (b : α), D₁.predCost A b = D₂.predCost A b

/-- Two weighted systems have equivalent closure membership on Finsets. -/
def ClosureMemberEquiv (D₁ D₂ : WeightedClosureDep α) : Prop :=
  ∀ (A : Finset α) (b : α), b ∈ D₁.cl ↑A ↔ b ∈ D₂.cl ↑A

end WeightedClosureDep

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

/-- The canonical sparse predictor basis: all pairs `(A, b)` where `A` is
a minimal support for `b`. -/
def canonicalBasis (C : ClosureSys α) : Set (Finset α × α) :=
  {p | IsMinimalSupport C p.1 p.2}


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

/-- A closed set `F` is join-irreducible in the closure lattice: it is
not the bottom element and cannot be written as the join (= closure of union)
of two strictly smaller closed sets. -/
def ClosedJoinIrred (C : ClosureSys α) (F : Set α) : Prop :=
  C.IsClosed F ∧ F ≠ C.cl ∅ ∧
    ∀ G H : Set α, C.IsClosed G → C.IsClosed H →
      C.cl (G ∪ H) = F → G = F ∨ H = F


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

/-! ## §8. Cost-Controlled Exchange

A strengthening of the exchange axiom with cost bounds. -/

/-
Standard exchange implies existence of a reverse derivation element.
-/

/-! ## §9. Sparse Predictor Extraction Under Exchange

When the closure system has exchange, minimal supports enjoy stronger
properties enabling certified sparse predictor extraction. -/

/-
Under exchange, for a minimal support, each element is re-derivable
from the support using the original element (self-consistency).
-/

/-
Two elements in a minimal support under exchange are "co-dependent":
each can be re-derived in the presence of the target.
-/

end Bridges.AlgebraEMLMachineLearning.ClosureDependency


