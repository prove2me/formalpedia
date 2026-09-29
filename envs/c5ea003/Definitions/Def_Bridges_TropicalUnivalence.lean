-- Prove2me | Definitions.Def_Bridges_TropicalUnivalence
-- name    : Bridges_TropicalUnivalence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:53.34129+00:00
-- url     : https://prove2.me/theorems/2fe752ad-0922-45fe-8eb2-6a7319a08cca
-- title:
--   Aether Catalog definitions — Bridges_TropicalUnivalence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalUnivalence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalUnivalence.lean by skeleton subtraction
import Mathlib
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

/-- Apply a permutation to a weighted matrix by simultaneously permuting
    rows and columns. This is the tropical analogue of transport along
    an equivalence in HoTT. -/
def permuteMatrix {n : ℕ} (D : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℕ :=
  fun i j => D (σ i) (σ j)

/-- Two finite weighted spaces (encoded as matrices) are tropically equivalent
    if there exists a permutation preserving all distances. This is the tropical
    analogue of type equivalence in HoTT. -/
def tropicallyEquivalent {n : ℕ} (D E : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i j, E (σ i) (σ j) = D i j


/-- The orbit code of a matrix: the set of all matrices obtainable by
    permutation. This serves as the canonical tropical identity code.
    Two matrices have the same orbit code iff they are tropically equivalent. -/
noncomputable def orbitCode {n : ℕ} (D : Matrix (Fin n) (Fin n) ℕ) :
    Finset (Matrix (Fin n) (Fin n) ℕ) :=
  Finset.univ.image (fun σ => permuteMatrix D σ)

/-- A matrix is a valid tropical distance matrix: zero diagonal and symmetric. -/
def IsTropicalDistanceMatrix {n : ℕ} (D : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  D.IsSymm ∧ ∀ i, D i i = 0

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

/-- **Tropical equivalence is decidable.** This is the computational core of
    tropical univalence: unlike classical path types which are generally
    undecidable, tropical equivalence can be decided by exhaustive search
    over the finite permutation group.

    This connects tropical HoTT to algorithmic graph isomorphism and
    makes the univalence principle executable. -/
instance tropicalEquivalentDecidable {n : ℕ}
    (D E : Matrix (Fin n) (Fin n) ℕ) :
    Decidable (tropicallyEquivalent D E) :=
  Fintype.decidableExistsFintype

/-- The distance-matrix property is decidable. -/
instance isTropicalDistanceMatrix_decidable {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℕ) :
    Decidable (IsTropicalDistanceMatrix D) := by
  unfold IsTropicalDistanceMatrix
  exact instDecidableAnd

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


