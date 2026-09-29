-- Prove2me | solution 1 for FinitaryExchangeClosure.closed_iff_rank_strict_increase
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:08:33.270207+00:00
-- url     : https://prove2.me/submissions/9f15a8d9-ace9-4a96-bb81-62f61f901b8c

-- Sol generated from Bridges/ClosureMatroidSecretSharing.lean
import Mathlib
import Definitions.Def_Bridges_ClosureMatroidSecretSharing
import Theorems.Thm_FinitaryExchangeClosure_spanning_of_rank_achieving

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
theorem cl_subset_cl_of_subset_cl {A B : Set X} (h : A ⊆ C.cl B) :
    C.cl A ⊆ C.cl B := by
  have := C.monotone h;
  rwa [ C.idempotent ] at this

/-- Closure is monotone (named for dot notation). -/
theorem cl_mono {A B : Set X} (h : A ⊆ B) : C.cl A ⊆ C.cl B :=
  C.monotone h

/-
`x ∈ cl A` iff `cl (A ∪ {x}) = cl A`.
-/

/-! ## 4. Independence Lemmas -/

/-- The empty set is independent. -/
theorem independent_empty : C.Independent ∅ := by
  intro x hx; simp at hx

/-
Subsets of independent sets are independent (hereditary property).
-/
theorem independent_subset {A B : Set X} (hA : C.Independent A) (hB : B ⊆ A) :
    C.Independent B := by
  intro x hx;
  have := hA x ( hB hx );
  exact fun h => this ( cl_mono C ( Set.diff_subset_diff_left hB ) h )

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
theorem rank_set_bddAbove (A : Set X) :
    BddAbove {n : ℕ | ∃ I : Finset X, (↑I : Set X) ⊆ A ∧ C.Independent (↑I) ∧ I.card = n} := by
  exact ⟨ Fintype.card X, by rintro n ⟨ I, hI₁, hI₂, rfl ⟩ ; exact Finset.card_le_univ _ ⟩

/-
The set of cardinalities of independent subsets of A is nonempty.
-/
theorem rank_set_nonempty (A : Set X) :
    {n : ℕ | ∃ I : Finset X, (↑I : Set X) ⊆ A ∧ C.Independent (↑I) ∧ I.card = n}.Nonempty := by
  -- The empty set is a finite subset of A and is independent.
  use 0
  use ∅
  simp [independent_empty C]

/-
The rank of a set is achieved by some independent subset.
-/
theorem rank_achieved (A : Set X) :
    ∃ I : Finset X, (↑I : Set X) ⊆ A ∧ C.Independent (↑I) ∧ I.card = C.rank A := by
  convert Nat.sSup_mem ?_ ?_;
  any_goals exact { n | ∃ I : Finset X, ( I : Set X ) ⊆ A ∧ C.Independent ( I : Set X ) ∧ I.card = n };
  · exact?;
  · exact?;
  · exact ⟨ _, fun n hn => hn.choose_spec.2.2 ▸ Finset.card_le_univ _ ⟩

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
theorem solution(F : Set X) :
    C.Closed F ↔ ∀ x ∉ F, C.rank (F ∪ {x}) = C.rank F + 1 := by
  constructor;
  · intro hF x hx
    have h_insert : C.rank (F ∪ {x}) ≥ C.rank F + 1 := by
      obtain ⟨ I, hI_sub, hI_ind, hI_rank ⟩ := rank_achieved C F;
      have h_insert : C.Independent (↑I ∪ {x}) := by
        apply independent_insert_of_not_mem_cl C hI_ind;
        have h_cl_I_subset_F : C.cl (↑I) ⊆ F := by
          have h_cl_I_subset_F : C.cl (↑I) ⊆ C.cl F := by
            exact cl_mono C hI_sub;
          exact h_cl_I_subset_F.trans ( hF.symm ▸ Set.Subset.refl _ );
        exact fun h => hx <| h_cl_I_subset_F h;
      refine' le_csSup _ _;
      · exact ⟨ _, fun n hn => hn.choose_spec.2.2 ▸ Finset.card_le_univ _ ⟩;
      · refine' ⟨ Insert.insert x I, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, Set.subset_def ];
        rw [ Finset.card_insert_of_notMem ( fun h => hx ( hI_sub x h ) ), hI_rank ];
    refine' le_antisymm _ h_insert;
    refine' csSup_le' _;
    rintro n ⟨ I, hI₁, hI₂, rfl ⟩;
    by_cases hxI : x ∈ I;
    · have hI_minus_x : (I.erase x : Set X) ⊆ F := by
        intro y hy; specialize hI₁ ( Finset.mem_of_mem_erase hy ) ; aesop;
      have hI_minus_x_rank : (I.erase x).card ≤ C.rank F := by
        exact le_csSup ( rank_set_bddAbove C F ) ⟨ I.erase x, hI_minus_x, independent_subset C hI₂ ( by aesop ), rfl ⟩;
      rw [ Finset.card_erase_of_mem hxI ] at hI_minus_x_rank ; omega;
    · exact le_add_of_le_of_nonneg ( le_csSup ( rank_set_bddAbove C F ) ⟨ I, fun y hy => by have := hI₁ hy; aesop, hI₂, rfl ⟩ ) zero_le_one;
  · intro h
    by_contra h_not_closed
    obtain ⟨x, hx⟩ : ∃ x, x ∈ C.cl F ∧ x ∉ F := by
      exact Set.exists_of_ssubset ( lt_of_le_of_ne ( C.extensive F ) ( Ne.symm h_not_closed ) )
    generalize_proofs at *;
    -- By rank_achieved, get J ⊆ F ∪ {x} independent with J.card = rank F + 1.
    obtain ⟨J, hJ_sub, hJ_ind, hJ_card⟩ : ∃ J : Finset X, (↑J : Set X) ⊆ F ∪ {x} ∧ C.Independent (↑J) ∧ J.card = C.rank (F ∪ {x}) := by
      exact?
    generalize_proofs at *;
    -- Since J is independent and x ∈ J, we have J \ {x} ⊆ F is independent with (J \ {x}).card = rank F.
    have hJ_erase_ind : C.Independent (↑(J.erase x)) := by
      exact independent_subset C hJ_ind ( by aesop_cat )
    have hJ_erase_card : (J.erase x).card = C.rank F := by
      by_cases hxJ : x ∈ J <;> simp_all +decide [ Finset.card_erase_of_mem ];
      have hJ_subset_F : (J : Set X) ⊆ F := by
        grind
      generalize_proofs at *;
      have hJ_card_le : J.card ≤ C.rank F := by
        exact le_csSup ( rank_set_bddAbove C F ) ⟨ J, hJ_subset_F, hJ_ind, rfl ⟩
      generalize_proofs at *;
      linarith;
    generalize_proofs at *;
    -- By spanning_of_rank_achieving applied to F and J.erase x, F ⊆ cl(↑(J.erase x)).
    have hF_subset_cl_J_erase : F ⊆ C.cl (↑(J.erase x)) := by
      apply spanning_of_rank_achieving
      generalize_proofs at *;
      · intro y hy; specialize hJ_sub ( Finset.mem_of_mem_erase hy ) ; aesop;
      · exact hJ_erase_ind;
      · exact hJ_erase_card
    generalize_proofs at *;
    -- Then x ∈ cl F ⊆ cl(cl(↑(J.erase x))) = cl(↑(J.erase x)).
    have hx_cl_J_erase : x ∈ C.cl (↑(J.erase x)) := by
      exact cl_subset_cl_of_subset_cl C hF_subset_cl_J_erase hx.1
    generalize_proofs at *;
    have := hJ_ind x; simp_all +decide [ Set.subset_def ] ;
