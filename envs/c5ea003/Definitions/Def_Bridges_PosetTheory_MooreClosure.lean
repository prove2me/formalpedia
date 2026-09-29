-- Prove2me | Definitions.Def_Bridges_PosetTheory_MooreClosure
-- name    : Bridges_PosetTheory_MooreClosure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:22.546426+00:00
-- url     : https://prove2.me/theorems/af35355d-e6e3-442c-bbd0-8b18ced95530
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_MooreClosure
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.MooreClosure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/MooreClosure.lean by skeleton subtraction
import Mathlib
/-
# Moore Family Closure Operator

This file formalizes the Moore family theorem: given a predicate `Closed : Set α → Prop`
that is preserved by arbitrary intersections and holds for `univ`, the hull
`mooreClosure Closed A = ⋂₀ {s | Closed s ∧ A ⊆ s}` defines a closure operator,
and the closed sets form a complete lattice under inclusion.

## Main results

* `mooreClosure_extensive` — `A ⊆ mooreClosure Closed A`
* `mooreClosure_closed` — `Closed (mooreClosure Closed A)`
* `mooreClosure_minimal` — if `Closed B` and `A ⊆ B` then `mooreClosure Closed A ⊆ B`
* `mooreClosure_mono` — monotonicity of the closure operator
* `mooreClosure_idempotent` — `mooreClosure Closed (mooreClosure Closed A) = mooreClosure Closed A`
* `mooreClosure_eq_iff` — `mooreClosure Closed A = A ↔ Closed A`
* `fixedPoints_sInter_closed` — fixed points of a closure operator are closed under `⋂₀`
* `mooreClosedSetsCompleteLattice` — the subtype of closed sets is a `CompleteLattice`

## Concrete instantiation

* `ClosedMulId` — multiplicatively closed matrix classes containing the identity
* `closedMulId_univ`, `closedMulId_sInter` — Moore family axioms for `ClosedMulId`
-/

open Set

/-! ## Definition of Moore closure -/

/-- The Moore closure of a set `A` with respect to a closedness predicate:
    the intersection of all closed supersets of `A`. -/
def mooreClosure {α : Type*} (Closed : Set α → Prop) (A : Set α) : Set α :=
  ⋂₀ {s : Set α | Closed s ∧ A ⊆ s}

/-! ## Core closure operator properties -/

/-
The Moore closure is extensive: `A ⊆ mooreClosure Closed A`.
-/

/-
The Moore closure of any set is closed.
-/

/-
The Moore closure is the smallest closed superset.
-/

/-
The Moore closure is idempotent.
-/

/-
The Moore closure is monotone.
-/

/-! ## Fixed-point characterization -/

/-
A set is closed if and only if it equals its own Moore closure.
-/

/-! ## Galois-style minimality: fixed points of a closure operator form a Moore family -/

/-
If `c` is an extensive, monotone, idempotent operator, then the family of its
    fixed points (`c s = s`) is closed under arbitrary intersections.
-/

/-! ## Complete lattice on the subtype of Moore-closed sets -/



/-! ## Concrete instantiation: multiplicatively closed matrix classes -/

/-- A set of 3×3 integer matrices is multiplicatively closed with identity if it
    contains the identity matrix and is closed under matrix multiplication. -/
def ClosedMulId (S : Set (Matrix (Fin 3) (Fin 3) ℤ)) : Prop :=
  (1 ∈ S) ∧ ∀ ⦃A B⦄, A ∈ S → B ∈ S → A * B ∈ S

/-
`ClosedMulId` holds for `univ`.
-/

/-
`ClosedMulId` is preserved by arbitrary intersections.
-/



/-! ## Concrete instantiation: orbit-stable classes -/

/-- A set is closed under a transformation `T` if applying `T` to any member
    stays in the set. -/
def ClosedUnderT {α : Type*} (T : α → α) (S : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ S → T x ∈ S

/-
`ClosedUnderT T` holds for `univ`.
-/

/-
`ClosedUnderT T` is preserved by arbitrary intersections.
-/


