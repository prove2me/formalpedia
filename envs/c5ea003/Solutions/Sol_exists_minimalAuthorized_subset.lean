-- Prove2me | solution 1 for exists_minimalAuthorized_subset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:09:31.096377+00:00
-- url     : https://prove2.me/submissions/a14475c1-66c9-4c6d-9a91-90d48df15ef8

-- Sol generated from Bridges/ClosureSecretSharingDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureSecretSharingDuality
/-
# Closure–Secret-Sharing Duality via Idempotent Dependency Systems

This module establishes a formal duality between:
- **Finite monotone access structures** (the cryptographic side),
- **Closure operators on pointed participant sets** (the geometric side),
- **Pointed dependency systems** (the algebraic side).

The main results:
1. Authorization induced by a closure operator is monotone (upward-closed).
2. Minimal authorized sets are exactly the "secret-circuits" of the closure geometry.
3. Every pointed dependency system induces a closure-exact access structure.
4. Every closure-exact access structure admits a pointed dependency representation.
5. Certified enumeration of minimal authorized sets.

## Key Insight

A secret-sharing access structure is not just *representable* by closure data —
it *is* a pointed closure geometry. Authorization means "the secret lies in the
span of the chosen participants," and unauthorized sets are exactly the flats
avoiding the secret.
-/


open Set Function

universe u

/-! ## §1 Closure Operators -/


/-! ## §2 Lifting participants and authorization -/




/-! ## §3 Monotonicity and complement lemmas -/




/-! ## §4 Minimal authorized sets and secret-circuits -/



/-
**Theorem 2**: Minimal authorized sets are exactly the secret-circuits
    of the closure geometry.
-/

/-! ## §5 Pointed Dependency Systems -/




/-! ## §6 From Dependency Systems to Closure Operators -/


/-
The closure operator induced by a dependency system is indeed a closure operator.
-/

/-
**Theorem 3**: A dependency system's authorization agrees with the
    closure-based authorization from the induced closure operator.
-/

/-! ## §7 From Closure Operators to Dependency Systems -/


/-
**Theorem 4 (forward)**: The dependency system from a closure operator
    recovers the same authorization predicate.
-/

/-! ## §8 Closure-Exact Access Structures -/




/-! ## §9 Round-trip: closure → dependency → closure preserves authorization -/

/-
The round-trip closure → dependency → closure recovers the original authorization.
-/

/-
The round-trip dependency → closure → dependency recovers the original authorization.
-/

/-! ## §10 Minimal authorized sets: finitary structure -/

/-
Every authorized set in a closure-exact access structure contains
    a minimal authorized subset (finite case).
-/

/-! ## §11 Irredundant presentations -/



/-! ## §12 Summary: the main duality theorem -/


theorem solution    {X : Type u} [Finite X]
    (cl : Set (Option X) → Set (Option X))
    (_hcl : IsClosureOperator cl)
    (S : Finset X)
    (hS : AuthorizedFromClosure cl (↑S : Set X)) :
    ∃ T : Finset X, ↑T ⊆ (↑S : Set X) ∧
      IsMinimalAuthorized (AuthorizedFromClosure cl) (↑T : Set X) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset X, T ⊆ S ∧ AuthorizedFromClosure cl T ∧ ∀ T' : Finset X, T' ⊂ T → ¬ AuthorizedFromClosure cl T' := by
    obtain ⟨T, hT⟩ : ∃ T : Finset X, T ⊆ S ∧ AuthorizedFromClosure cl T ∧ ∀ T' : Finset X, T' ⊆ S → AuthorizedFromClosure cl T' → T.card ≤ T'.card := by
      have h_min : ∃ T ∈ {T : Finset X | T ⊆ S ∧ AuthorizedFromClosure cl T}, ∀ T' ∈ {T : Finset X | T ⊆ S ∧ AuthorizedFromClosure cl T}, T.card ≤ T'.card := by
        apply_rules [ Set.exists_min_image ];
        · exact Set.Finite.subset ( Set.toFinite ( Finset.powerset S ) ) fun T hT => Finset.mem_powerset.mpr hT.1;
        · exact ⟨ S, Finset.Subset.refl _, hS ⟩;
      grind;
    exact ⟨ T, hT.1, hT.2.1, fun T' hT' hT'' => not_lt_of_ge ( hT.2.2 T' ( Finset.Subset.trans hT'.1 hT.1 ) hT'' ) ( Finset.card_lt_card hT' ) ⟩;
  use T; simp_all +decide [ IsMinimalAuthorized ] ;
  intro T' hT' hT'_auth
  obtain ⟨T'_fin, hT'_fin⟩ : ∃ T'_fin : Finset X, T' = T'_fin := by
    exact ⟨ Set.Finite.toFinset ( Set.Finite.subset ( Finset.finite_toSet T ) hT'.1 ), by simp ⟩
  generalize_proofs at *;
  exact hT.2.2 T'_fin ( by simpa [ hT'_fin ] using hT' ) ( by simpa [ hT'_fin ] using hT'_auth )
