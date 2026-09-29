-- Prove2me | solution 1 for FinitaryExchangeClosure.rank_union_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:08:34.349434+00:00
-- url     : https://prove2.me/submissions/6a70966b-8a10-4290-903e-34f9a51f7d4e

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
theorem solution(A B : Set X) :
    C.rank (A ∪ B) ≤ C.rank A + C.rank B := by
  nontriviality;
  refine' csSup_le ( rank_set_nonempty C _ ) _;
  norm_num +zetaDelta at *;
  intros b x hx_sub hx_ind hx_card;
  obtain ⟨ y, hy_sub, hy_ind, hy_card ⟩ := rank_achieved C ( A ∩ x );
  -- Since $y \subseteq A \cap x$ and $x \subseteq A \cup B$, we have $x \setminus y \subseteq B$.
  have hxy_sub_B : (x \ y : Set X) ⊆ B := by
    intro z hz;
    cases hx_sub hz.1 <;> simp_all +decide [ Set.subset_def ];
    contrapose! hy_card;
    refine' ne_of_lt ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ _, _ ⟩ ) ) ( le_csSup _ _ ) );
    exact Insert.insert z y;
    · exact Finset.subset_insert _ _;
    · exact fun h => hz.2 ( h.symm ▸ Finset.mem_insert_self _ _ );
    · exact ⟨ _, fun n hn => hn.choose_spec.2.2 ▸ Finset.card_le_card ( show hn.choose ⊆ x from fun a ha => hn.choose_spec.1 ha |>.2 ) ⟩;
    · refine' ⟨ Insert.insert z y, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, Set.subset_def ];
      grind +suggestions;
  -- Since $x \setminus y$ is independent and a subset of $B$, we have $\text{rank}(B) \geq \text{card}(x \setminus y)$.
  have h_rank_B_ge_card_x_minus_y : C.rank B ≥ (x \ y : Finset X).card := by
    refine' le_csSup _ _;
    · exact ⟨ Finset.card ( Finset.univ : Finset X ), by rintro n ⟨ I, hI_sub, hI_ind, rfl ⟩ ; exact Finset.card_le_univ _ ⟩;
    · refine' ⟨ x \ y, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      exact independent_subset C hx_ind fun z hz => by aesop;
  have h_rank_A_ge_card_y : C.rank A ≥ y.card := by
    refine' le_csSup _ _;
    · exact ⟨ _, fun n hn => hn.choose_spec.2.2 ▸ Finset.card_le_univ _ ⟩;
    · exact ⟨ y, fun z hz => hy_sub hz |>.1, hy_ind, rfl ⟩;
  grind
