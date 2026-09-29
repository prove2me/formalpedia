-- Prove2me | Definitions.Def_Bridges_ClosureMatroidSecretSharing
-- name    : Bridges_ClosureMatroidSecretSharing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:11.646556+00:00
-- url     : https://prove2.me/theorems/a3c7ca1b-69ea-488b-8b65-b938747e09cf
-- title:
--   Aether Catalog definitions — Bridges_ClosureMatroidSecretSharing
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureMatroidSecretSharing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureMatroidSecretSharing.lean by skeleton subtraction
import Mathlib

/-!
# Closure–Matroid–Secret Sharing Bridge

## Overview

This module establishes a formal bridge between finite exchange closure operators,
matroid geometry, and cryptographic secret-sharing access structures, mediated by
an idempotent algebraic structure on closed sets.

## Main results

- **Exchange closures induce matroidal geometry**: independence, rank, flats, and circuits
  arise canonically from the closure axioms.
- **Certified access structures**: for a designated "dealer" element `d`, the set of
  subsets that span `d` under closure forms a monotone access structure with
  formally certified reconstruction (qualified sets are upward-closed) and
  privacy (non-spanning sets are downward-closed).
- **Minimal qualified sets are minimal dependent sets through the dealer**: the
  circuit-like characterization of minimal reconstruction sets.
- **Rank-bounded reconstruction**: every qualified set contains a minimal qualified
  subset of cardinality at most the global rank.
- **Idempotent closed-set algebra**: closed sets form a lattice under join = closure
  of union and meet = intersection, with provable algebraic laws.

## Mathematical significance

Every finite exchange closure is not just a combinatorial geometry, but a certified
cryptographic universe in which reconstruction, privacy, and complexity are all
controlled by closure and rank. This reframes secret-sharing as resource-sensitive
entailment in a finite closure logic, with matroids providing the geometric backbone.
-/

open Set Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## 1. Finitary Exchange Closure Structure -/

/-- A finitary exchange closure operator on a finite type.
This is the standard axiomatization that gives rise to matroid geometry. -/
structure FinitaryExchangeClosure (X : Type*) [Fintype X] where
  /-- The closure operator -/
  cl : Set X → Set X
  /-- Every set is contained in its closure -/
  extensive : ∀ A, A ⊆ cl A
  /-- Closure is monotone -/
  monotone : ∀ {A B : Set X}, A ⊆ B → cl A ⊆ cl B
  /-- Closure is idempotent -/
  idempotent : ∀ A, cl (cl A) = cl A
  /-- The Steinitz–Mac Lane exchange axiom -/
  exchange : ∀ A x y, x ∉ cl A → x ∈ cl (A ∪ {y}) → y ∈ cl (A ∪ {x})

namespace FinitaryExchangeClosure

variable (C : FinitaryExchangeClosure X)

/-! ## 2. Basic Definitions -/

/-- A set is closed if it equals its own closure. -/
def Closed (A : Set X) : Prop := C.cl A = A

/-- A set is independent if no element is in the closure of the rest. -/
def Independent (A : Set X) : Prop :=
  ∀ x ∈ A, x ∉ C.cl (A \ {x})

/-- A set qualifies for reconstruction of dealer `d` if `d` is in its closure. -/
def Qualified (d : X) (A : Set X) : Prop := d ∈ C.cl A

/-- A set is private w.r.t. dealer `d` if `d` is not in its closure. -/
def Private (d : X) (A : Set X) : Prop := d ∉ C.cl A

/-- A minimal qualified set: qualifies, but no proper subset does. -/
def MinimalQualified (d : X) (A : Set X) : Prop :=
  C.Qualified d A ∧ ∀ B, B ⊂ A → C.Private d B



/-! ## 3. Basic Closure Lemmas -/



/-
Closure of union absorbs inner closures (left).
-/

/-
Closure of union absorbs inner closures (right).
-/

/-
If `A ⊆ cl B` then `cl A ⊆ cl B`.
-/


/-
`x ∈ cl A` iff `cl (A ∪ {x}) = cl A`.
-/

/-! ## 4. Independence Lemmas -/


/-
Subsets of independent sets are independent (hereditary property).
-/

/-
If `I` is independent and `x ∉ cl I`, then `I ∪ {x}` is independent.
-/

/-
If `A` is independent, then `x ∈ cl A` iff `x ∈ A` or `A ∪ {x}` is dependent.
-/

/-! ## 5. Secret-Sharing Access Structure (Theorem 4) -/

/-
**Certified Access Structure**: qualification is upward-closed,
    private is downward-closed, and they partition all subsets.
    This is the foundational theorem for closure-based secret sharing.
-/

/-
**Certified Privacy**: non-spanning sets cannot leak the dealer.
    This is the exact privacy guarantee: no subset of a private set is qualified.
-/

/-
**Reconstruction monotonicity**: if a subset can reconstruct, so can any superset.
-/

/-! ## 6. Rank Function -/

/-- The rank of a set is the maximum cardinality of an independent subset.
    Well-defined for finite types. -/
noncomputable def rank (A : Set X) : ℕ :=
  sSup {n : ℕ | ∃ I : Finset X, (↑I : Set X) ⊆ A ∧ C.Independent (↑I) ∧ I.card = n}

/-
Rank is bounded by cardinality.
-/

/-
Rank is monotone.
-/

/-
The empty set has rank zero.
-/

/-
Rank of a singleton is at most 1.
-/

/-
The set of cardinalities of independent subsets of A is bounded above.
-/

/-
The set of cardinalities of independent subsets of A is nonempty.
-/

/-
The rank of a set is achieved by some independent subset.
-/

/-
A rank-achieving independent subset spans the whole set under closure.
-/

/-! ## 7. Closed Sets and Flats (Theorem 2) -/

/-
A closed set `F` has the property that adding any element outside `F` strictly
    increases the rank. This characterizes flats / dependency flats.
-/

/-
Intersection of closed sets is closed.
-/

/-! ## 8. Minimal Qualified Sets and Circuits (Theorem 3) -/

/-
Every qualified set contains a minimal qualified subset.
-/

/-
Minimal qualified sets are minimal dependent sets that include the dealer
    in their closure.
-/

/-! ## 9. Rank-Bounded Reconstruction (Theorem 5) -/

/-
**Rank-bounded reconstruction**: every qualified set contains a minimal qualified
    subset whose cardinality is bounded by the global rank.
    This is the certified reconstruction complexity theorem.
-/

/-! ## 10. Idempotent Closed-Set Algebra -/

/-- Dependency addition: closure of union. -/
def depAdd (A B : Set X) : Set X := C.cl (A ∪ B)

/-- Dependency meet: closure of intersection. -/
def depMul (A B : Set X) : Set X := C.cl (A ∩ B)

/-
`depAdd` is commutative.
-/

/-
`depAdd` is associative.
-/

/-
`depAdd` is idempotent on closed sets.
-/

/-
`depMul` is commutative.
-/

/-
`depMul` is idempotent on closed sets.
-/

/-
Closed sets form a join-semilattice with join = depAdd and meet = intersection.
    `depMul` on closed sets equals intersection.
-/

/-
`depAdd` absorbs `depMul` on closed sets.
-/

/-
Rank is subadditive under union:
    `rank(A ∪ B) ≤ rank A + rank B`.
-/

end FinitaryExchangeClosure


