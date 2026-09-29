-- Prove2me | solution 1 for FinitaryExchangeClosure.exists_minimalQualified_card_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:08:33.848546+00:00
-- url     : https://prove2.me/submissions/38ddd2b2-b0ca-42a4-b6a7-2e86ffd1e36e

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
theorem mem_cl_iff_cl_insert (A : Set X) (x : X) :
    x ∈ C.cl A ↔ C.cl (A ∪ {x}) = C.cl A := by
  refine' ⟨ fun hx => _, fun hx => _ ⟩;
  · refine' Set.Subset.antisymm _ _;
    · exact cl_subset_cl_of_subset_cl C ( Set.union_subset ( C.extensive _ ) ( Set.singleton_subset_iff.2 hx ) );
    · exact cl_mono C ( Set.subset_union_left );
  · exact hx ▸ C.extensive _ ( Set.mem_union_right _ ( Set.mem_singleton _ ) )

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
theorem exists_minimalQualified_subset (d : X) (A : Set X)
    (hA : C.Qualified d A) (hfin : A.Finite) :
    ∃ B ⊆ A, C.MinimalQualified d B := by
  -- By the well-foundedness of the powerset of a finite set, there exists a minimal subset of $A$ that is qualified.
  obtain ⟨B, hB⟩ : ∃ B ∈ {B : Set X | B ⊆ A ∧ d ∈ C.cl B}, ∀ C' ∈ {B : Set X | B ⊆ A ∧ d ∈ C.cl B}, ¬(C' ⊂ B) := by
    have h_well_founded : WellFounded (fun B C : Set X => B ⊂ C) := by
      exact?;
    exact h_well_founded.has_min _ ⟨ A, ⟨ Set.Subset.refl _, hA ⟩ ⟩;
  refine' ⟨ B, hB.1.1, hB.1.2, fun C' hC' => _ ⟩;
  exact fun h => hB.2 C' ⟨ hC'.1.trans hB.1.1, h ⟩ hC'

/-
Minimal qualified sets are minimal dependent sets that include the dealer
    in their closure.
-/
theorem minimalQualified_iff_minimal_dep_spanning_dealer
    (d : X) (A : Set X) :
    C.MinimalQualified d A ↔
    C.Qualified d A ∧ C.Independent (A \ {d}) ∧
    ∀ B, B ⊂ A → C.Private d B := by
  refine' ⟨ fun h => ⟨ h.1, _, h.2 ⟩, fun h => ⟨ h.1, h.2.2 ⟩ ⟩;
  intro x hx;
  have := h.2 ( A \ { x } ) ?_ <;> simp_all +decide [ Set.diff_subset_iff ];
  have h_closure : C.cl ((A \ {d}) \ {x}) ⊆ C.cl (A \ {x}) := by
    exact cl_mono C ( by aesop_cat );
  contrapose! this;
  have := mem_cl_iff_cl_insert C ( A \ { x } ) x; simp_all +decide [ Set.diff_subset_iff ] ;
  have := this.mp ( h_closure ‹_› ) ; simp_all +decide [ FinitaryExchangeClosure.Private ] ;
  exact this ▸ h.1

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


theorem exists_minimalQualified_subset_finset (d : X) (A : Finset X)
    (hA : C.Qualified d (↑A : Set X)) :
    ∃ B : Finset X, (B : Set X) ⊆ A ∧ C.MinimalQualified d B := by
  have key : ∀ n : ℕ, ∀ t : Finset X, C.Qualified d (↑t : Set X) → t.card = n →
      ∃ B : Finset X, B ⊆ t ∧ C.Qualified d ↑B ∧
        ∀ T : Finset X, T ⊂ B → ¬ C.Qualified d ↑T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t hq hcard
      by_cases hmin : ∃ B : Finset X, B ⊆ t ∧ C.Qualified d ↑B ∧
          ∀ T : Finset X, T ⊂ B → ¬ C.Qualified d ↑T
      · exact hmin
      · push_neg at hmin
        obtain ⟨T, hT₁, hT₂⟩ := hmin t (Finset.Subset.refl t) hq
        have hlt : T.card < n := by
          have hlt0 : T.card < t.card := Finset.card_lt_card hT₁
          rw [hcard] at hlt0
          exact hlt0
        obtain ⟨B, hB₁, hB₂, hB₃⟩ := ih _ hlt T hT₂ rfl
        exact ⟨B, hB₁.trans hT₁.1, hB₂, hB₃⟩
  obtain ⟨B, hB₁, hBq, hBmin⟩ := key A.card A hA rfl
  refine ⟨B, Finset.coe_subset.mpr hB₁, hBq, ?_⟩
  intro S hS hSd
  obtain ⟨T, rfl⟩ := Set.Finite.exists_finset_coe
    (Set.Finite.subset (Finset.finite_toSet B) hS.1)
  rw [Finset.coe_ssubset] at hS
  exact hBmin T hS hSd

theorem minimalQualified_indep_diff_dealer (d : X) {B : Set X}
    (h : C.MinimalQualified d B) : C.Independent (B \ {d}) := by
  obtain ⟨hq, hmin⟩ := h
  intro x hx hmem
  have hxB : x ∈ B := ((Set.mem_diff x).mp hx).1
  have h1 : x ∈ C.cl (B \ {x}) :=
    C.monotone (Set.diff_subset_diff_left Set.diff_subset) hmem
  have h2 : B ⊆ C.cl (B \ {x}) := by
    intro y hy
    by_cases hyx : y = x
    · rw [hyx]; exact h1
    · exact C.extensive _ ((Set.mem_diff y).mpr ⟨hy, hyx⟩)
  have h3 : d ∈ C.cl (B \ {x}) := by
    have h4 : d ∈ C.cl (C.cl (B \ {x})) := C.monotone h2 hq
    rwa [C.idempotent] at h4
  have hne : (B \ {x} : Set X) ≠ B := by
    intro e
    have hx' : x ∈ (B \ {x} : Set X) := by rw [e]; exact hxB
    exact ((Set.mem_diff x).mp hx').2 rfl
  exact hmin _ (Set.ssubset_iff_subset_ne.mpr ⟨Set.diff_subset, hne⟩) h3

open FinitaryExchangeClosure in
theorem solution(d : X) (A : Finset X)
    (hA : C.Qualified d (↑A : Set X)) :
    ∃ B : Finset X, (↑B : Set X) ⊆ ↑A ∧
    C.MinimalQualified d (↑B) ∧
    B.card ≤ C.rank Set.univ := by
  have h_minimalQualified_subset : ∃ B : Finset X, (B : Set X) ⊆ A ∧ C.MinimalQualified d B :=
    exists_minimalQualified_subset_finset C d A hA
  obtain ⟨B, hB_subset, hB_min⟩ := h_minimalQualified_subset
  have hB_card : B.card ≤ C.rank Set.univ := by
    have hB_card : C.Independent (↑(B \ {d}) : Set X) := by
      rw [Finset.coe_sdiff, Finset.coe_singleton]
      exact minimalQualified_indep_diff_dealer C d hB_min
    have hB_card_le_rank : (B \ {d}).card ≤ C.rank Set.univ := by
      refine' le_csSup _ _;
      · exact ⟨ Finset.card ( Finset.univ : Finset X ), by rintro n ⟨ I, _, _, rfl ⟩ ; exact Finset.card_le_univ _ ⟩;
      · aesop
    have hB_card_le_rank_plus_one : B.card ≤ C.rank Set.univ + 1 := by
      grind
    by_cases hd : d ∈ B <;> simp_all +decide [ Finset.card_sdiff ];
    have := hB_min.2 ( B \ { d } ) ; simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ] ;
    have hB_card_le_rank : C.rank Set.univ ≥ (B \ {d}).card + 1 := by
      have hB_card_le_rank : ∃ I : Finset X, (I : Set X) ⊆ Set.univ ∧ C.Independent (I : Set X) ∧ I.card = (B \ {d}).card + 1 := by
        have hB_card_le_rank : C.Independent (↑(B \ {d} ∪ {d}) : Set X) := by
          rw [Finset.coe_union, Finset.coe_sdiff, Finset.coe_singleton]
          exact independent_insert_of_not_mem_cl C hB_card this;
        use B \ {d} ∪ {d};
        simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
        rw [ Nat.sub_add_cancel ( Finset.card_pos.mpr ⟨ d, hd ⟩ ) ];
      exact hB_card_le_rank.choose_spec.2.2 ▸ le_csSup ( by exact Set.Finite.bddAbove ( Set.finite_iff_bddAbove.mpr ⟨ Finset.card ( Finset.univ : Finset X ), by rintro n ⟨ I, hI₁, hI₂, rfl ⟩ ; exact Finset.card_le_univ _ ⟩ ) ) ⟨ _, hB_card_le_rank.choose_spec.1, hB_card_le_rank.choose_spec.2.1, rfl ⟩;
    grind
  use B
