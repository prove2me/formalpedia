-- Prove2me | solution 1 for tropical_plus_distributes_over_min
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:27:48.373926+00:00
-- url     : https://prove2.me/submissions/e592aa05-cf59-41e8-b393-b1567cb79382

-- Sol generated from Bridges/TropicalUnivalence.lean
import Mathlib
import Definitions.Def_Bridges_MinPlusVerificationCore
import Definitions.Def_Bridges_TropicalUnivalence
/-
# Tropical Univalence for Finite Weighted Spaces

This file establishes a tropical analogue of the Univalence Axiom from
Homotopy Type Theory. In HoTT, univalence states that equality of types
is equivalent to the existence of an equivalence between them. Here we prove:

> Two finite ℕ-weighted matrices are tropically equivalent (related by a
> distance-preserving permutation) if and only if their canonical orbit
> codes are equal.

This gives a concrete, decidable univalence principle for finite weighted
spaces: identity of tropical codes = existence of tropical isometry.

## Main results

* `tropicallyEquivalent_iff_orbitCode_eq` — the univalence theorem
* `tropicalEquivalentDecidable` — decidability of tropical equivalence
* `tropicallyEquivalent_refl/symm/trans` — equivalence relation structure
* `permuteMatrix_permuteMatrix` — composition of permutations
* `permuteMatrix_one` — identity permutation

## Cross-domain connections

The decidability theorem connects to:
- **Graph isomorphism**: tropical equivalence is metric-aware graph isomorphism
- **Phylogenetics**: tree metrics under taxon relabeling
- **Program equivalence**: cost-preserving behavioral equivalence of states
-/


open Equiv in

/-! ## Core Definitions -/






/-! ## Permutation Algebra -/

/-
The identity permutation leaves a matrix unchanged.
-/

/-
Composing two permutations on a matrix is the same as permuting by their product.
-/

/-
Permuting by the inverse recovers the original matrix.
-/

/-
Permutation preserves the symmetric property of a distance matrix.
-/

/-
Permutation preserves the zero-diagonal property.
-/

/-
Permutation preserves the tropical distance matrix property.
-/

/-! ## Tropical Equivalence is an Equivalence Relation -/

/-
Tropical equivalence is reflexive: every matrix is equivalent to itself
    via the identity permutation.
-/

/-
Tropical equivalence is symmetric: if D ≃ E then E ≃ D.
    Uses the inverse permutation.
-/

/-
Tropical equivalence is transitive: if D ≃ E and E ≃ F then D ≃ F.
    Uses composition of permutations.
-/

/-
Tropical equivalence as a bundled equivalence relation.
-/

/-! ## The Univalence Theorem: Orbit Code Classification -/

/-
A matrix belongs to its own orbit code.
-/

/-
If E is in the orbit of D, then D and E are tropically equivalent.
-/

/-
If D and E are tropically equivalent, then E is in the orbit of D.
-/

/-
If D and E are tropically equivalent, they have the same orbit code.
    This is the forward direction of univalence.
-/

/-
If orbit codes are equal, the matrices are tropically equivalent.
    This is the backward direction of univalence.
-/

/-
**Tropical Univalence Theorem**: Two finite weighted spaces have equal
    canonical orbit codes if and only if there exists a distance-preserving
    permutation between them. This is the tropical shadow of the Univalence
    Axiom from Homotopy Type Theory.

    In HoTT: (A = B) ≃ (A ≃ B)
    In tropical shadow: (orbitCode D = orbitCode E) ↔ tropicallyEquivalent D E
-/

/-! ## Decidability -/



/-! ## Gluing and Higher Structure -/

/-
Minimum distributes over addition: the fundamental tropical algebraic
    identity that governs path composition in the tropical shadow.
    In HoTT terms, this normalizes "path concatenation costs."
-/


/-
The glued distance at boundary points satisfies the normal form
    determined by tropical distribution.
-/

theorem solution(a b c : ℕ) :
    min (a + c) (b + c) = min a b + c := by
  bv_omega
