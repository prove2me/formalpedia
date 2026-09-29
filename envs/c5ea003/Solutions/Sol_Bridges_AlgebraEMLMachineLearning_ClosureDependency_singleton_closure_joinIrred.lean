-- Prove2me | solution 1 for Bridges.AlgebraEMLMachineLearning.ClosureDependency.singleton_closure_joinIrred
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T13:42:33.360867+00:00
-- url     : https://prove2.me/submissions/fa1db0e5-1e9c-45d6-b97b-b42ad2810b25

-- Sol generated from Bridges/ClosureDependency.lean
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


/-- The closure of any set is closed (idempotence). -/
theorem cl_isClosed (S : Set α) : C.IsClosed (C.cl S) := C.cl_idempotent S


/-
Intersection of two closed sets is closed.
-/

/-
Intersection of a nonempty family of closed sets is closed.
-/

/-
The closure is contained in any closed superset.
-/
theorem cl_le_of_subset_closed {S T : Set α} (hST : S ⊆ T) (hT : C.IsClosed T) :
    C.cl S ⊆ T := by
  exact hT ▸ C.cl_monotone hST

/-- Closure preserves membership for elements already in the set. -/
theorem mem_cl_of_mem {S : Set α} {x : α} (hx : x ∈ S) : x ∈ C.cl S :=
  C.cl_extensive S hx




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
set_option linter.unusedSectionVars false in
theorem exchange_symmetric_singleton (C : ClosureSys α)
    (hex : HasExchange C) (x y : α)
    (hy : y ∈ C.cl {x}) (hny : y ∉ C.cl ∅) :
    x ∈ C.cl {y} := by
  convert hex ∅ x y _ _ using 1 <;> aesop

/-
Under exchange, every proper closed subset of `cl({x})` (for `x ∉ cl(∅)`) is
contained in `cl(∅)`.
-/
theorem exchange_cl_singleton_minimal (C : ClosureSys α)
    (hex : HasExchange C) (x : α) (_hx : x ∉ C.cl ∅)
    (F : Set α) (hF : C.IsClosed F) (hFsub : F ⊆ C.cl {x}) (hFne : F ≠ C.cl {x}) :
    F ⊆ C.cl ∅ := by
  intro y hy;
  contrapose! hFne;
  have hx_in_F : x ∈ F := by
    have hx_in_F : x ∈ C.cl {y} := by
      apply exchange_symmetric_singleton C hex x y (hFsub hy) hFne;
    have hx_in_F : C.cl {y} ⊆ F := by
      exact cl_le_of_subset_closed C ( Set.singleton_subset_iff.mpr hy ) hF;
    exact hx_in_F ‹_›;
  refine' le_antisymm hFsub _;
  exact cl_le_of_subset_closed C ( Set.singleton_subset_iff.mpr hx_in_F ) hF

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


open Bridges.AlgebraEMLMachineLearning.ClosureDependency in
theorem solution(C : ClosureSys α)
    (hex : HasExchange C) (x : α) (hx : x ∉ C.cl ∅) :
    ClosedJoinIrred C (C.cl {x}) := by
  constructor;
  · exact cl_isClosed C _;
  · refine' ⟨ _, fun G H hG hH hGH => _ ⟩;
    · exact fun h => hx <| h ▸ mem_cl_of_mem C ( Set.mem_singleton x );
    · -- By exchange_cl_singleton_minimal, either G = cl({x}) or G ⊆ cl(∅). Similarly for H.
      have hG' : G = C.cl {x} ∨ G ⊆ C.cl ∅ := by
        have hG' : G ⊆ C.cl {x} := by
          exact hGH ▸ C.cl_extensive _ |> Set.Subset.trans ( Set.subset_union_left );
        exact Classical.or_iff_not_imp_left.2 fun h => exchange_cl_singleton_minimal C hex x hx G hG hG' h
      have hH' : H = C.cl {x} ∨ H ⊆ C.cl ∅ := by
        have hH' : H ⊆ C.cl {x} := by
          exact hGH ▸ C.cl_extensive _ |> Set.Subset.trans ( Set.subset_union_right );
        exact Classical.or_iff_not_imp_left.2 fun h => exchange_cl_singleton_minimal C hex x hx H hH hH' h;
      contrapose! hx;
      have h_union_subset : G ∪ H ⊆ C.cl ∅ := by
        exact Set.union_subset ( hG'.resolve_left hx.1 ) ( hH'.resolve_left hx.2 );
      have h_union_subset : C.cl (G ∪ H) ⊆ C.cl (C.cl ∅) := by
        exact C.cl_monotone h_union_subset;
      simp_all +decide [ C.cl_idempotent ];
      exact h_union_subset ( C.cl_extensive _ ( Set.mem_singleton _ ) )
