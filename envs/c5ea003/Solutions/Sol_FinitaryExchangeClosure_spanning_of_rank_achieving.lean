-- Prove2me | solution 1 for FinitaryExchangeClosure.spanning_of_rank_achieving
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:05:44.418226+00:00
-- url     : https://prove2.me/submissions/cf8399a8-1d47-4d3b-ac27-9991a29076a6

-- Sol generated from Bridges/ClosureMatroidSecretSharing.lean
import Mathlib
import Definitions.Def_Bridges_ClosureMatroidSecretSharing

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


open FinitaryExchangeClosure

variable (C : FinitaryExchangeClosure X)

/-! ## 2. Basic Definitions -/








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

/-- Closure is monotone (named for dot notation). -/
theorem cl_mono {A B : Set X} (h : A ⊆ B) : C.cl A ⊆ C.cl B :=
  C.monotone h

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
theorem independent_insert_of_not_mem_cl {I : Set X} {x : X}
    (hI : C.Independent I) (hx : x ∉ C.cl I) :
    C.Independent (I ∪ {x}) := by
  intro y hy; by_cases hyx : y = x <;> simp_all +decide [ Set.union_comm ] ;
  · exact fun h => hx ( cl_mono C ( Set.diff_subset ) h );
  · -- Since $y \in I$ and $y \neq x$, we have $I \setminus \{y\} \cup \{x\} \subseteq I \cup \{x\}$.
    have h_subset : insert x I \ {y} = insert x (I \ {y}) := by
      grind;
    have := C.exchange ( I \ { y } ) y x; simp_all +decide [ Set.insert_subset_iff ] ;
    exact this ( hI y hy )

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


open FinitaryExchangeClosure in
theorem solution{A : Set X} {I : Finset X}
    (hI_sub : (↑I : Set X) ⊆ A) (hI_ind : C.Independent (↑I))
    (hI_rank : I.card = C.rank A) :
    A ⊆ C.cl (↑I) := by
  intro y hyA;
  by_contra hy_not_cl;
  have h_indep : C.Independent (I ∪ {y}) := by
    exact?;
  have h_card : (I ∪ {y}).card = I.card + 1 := by
    exact Finset.card_union_of_disjoint ( Finset.disjoint_singleton_right.mpr fun h => hy_not_cl <| C.extensive _ h );
  have h_card_le : (I ∪ {y}).card ≤ C.rank A := by
    apply le_csSup;
    · exact ⟨ Finset.card ( Finset.univ : Finset X ), fun n hn => by obtain ⟨ I, hI_sub, hI_ind, rfl ⟩ := hn; exact Finset.card_le_univ _ ⟩;
    · exact ⟨ I ∪ { y }, by aesop_cat, by simpa using h_indep, by aesop_cat ⟩;
  grind +splitImp
