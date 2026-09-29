-- Prove2me | Definitions.Def_Bridges_TropicalValuationSecretSharingDuality
-- name    : Bridges_TropicalValuationSecretSharingDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:11.195431+00:00
-- url     : https://prove2.me/theorems/22c48f8e-e167-4fd9-a92a-89953e4da567
-- title:
--   Aether Catalog definitions — Bridges_TropicalValuationSecretSharingDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalValuationSecretSharingDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalValuationSecretSharingDuality.lean by skeleton subtraction
import Mathlib
/-
# Tropical Valuation Secret-Sharing Duality via Idempotent Access Semimodules
# and Certified Minimal Share Reconstruction

## Domain Bridge: Tropical Geometry ↔ Cryptographic Access Structures ↔ Idempotent Algebra

The central discovery: **Authorization in secret-sharing is an extremal attainability
phenomenon in max-plus linear algebra**, and **minimal share reconstruction is the
extraction of irreducible tropical generators**.

## Key Mathematical Insight:
Tropical access presentations with ∀-dimensional authorization naturally encode
**blocker-type** access structures: a coalition is authorized iff it intersects
every member of a blocking family. This is the Alexander dual perspective on
monotone access structures, and gives the correct bridge to tropical geometry.

## Main Results:
1. **Realization Theorem**: Tropical access presentations induce monotone access structures
   whose minimal authorized coalitions are exactly the extremal attainment sets.
2. **Reconstruction Theorem**: Every blocker-characterized access structure admits a canonical
   tropical access presentation that is generator-irredundant.
3. **Equivalence/Duality Theorem**: Reconstruction equivalence ↔ tropical semimodule isomorphism.

## Cross-Domain Connections:
- Builds on `TropicalOneWayFunctions` (tropical matrix/attainability lemmas)
- Uses `TropicalValuationFunctor` (valuation certificate infrastructure)
- Strengthens `finite_access_structure_has_closure_capacity_realization`
-/


open Finset BigOperators

noncomputable section

namespace TropicalSecretSharing

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ## §1. Core Definitions -/

/-- **Tropical Access Presentation**: A finite-dimensional tropical scheme.
    Each participant contributes a vector in ℕ^genDim, and authorization is
    checked against a threshold vector via max-plus scoring.

    **Connection to TropicalOneWayFunctions**: The matrix `mat` plays the role of a
    tropical matrix whose row support patterns determine attainability.
    **Connection to TropicalValuationFunctor**: The threshold `thresh` acts as a
    valuation certificate for minimum reconstruction depth. -/
structure TropicalAccessPresentation (P : Type*) [Fintype P] [DecidableEq P] where
  genDim : ℕ
  genDim_pos : 0 < genDim
  mat : P → Fin genDim → ℕ
  thresh : Fin genDim → ℕ
  thresh_pos : ∀ j, 0 < thresh j

/-- **Coalition Score**: max-plus score = sup of participant contributions. -/
def coalitionScore (A : TropicalAccessPresentation P) (C : Finset P) (j : Fin A.genDim) : ℕ :=
  C.sup (fun p => A.mat p j)

/-- **Authorization Predicate**: C is authorized iff score meets threshold in ALL dimensions. -/
def Authorized (A : TropicalAccessPresentation P) (C : Finset P) : Prop :=
  ∀ j : Fin A.genDim, A.thresh j ≤ coalitionScore A C j

instance authorizedDecidable (A : TropicalAccessPresentation P) (C : Finset P) :
    Decidable (Authorized A C) :=
  Fintype.decidableForallFintype

/-- **Minimal Authorized Coalition**: authorized with no authorized proper subset. -/
def MinimalAuthorized (A : TropicalAccessPresentation P) (C : Finset P) : Prop :=
  Authorized A C ∧ ∀ D : Finset P, D ⊂ C → ¬Authorized A D

/-- **Extremal Attainment Set**: authorized, and removing any participant breaks it. -/
def ExtremalAttainmentSet (A : TropicalAccessPresentation P) (C : Finset P) : Prop :=
  Authorized A C ∧ ∀ p ∈ C, ¬Authorized A (C.erase p)

/-- **Essential Share**: participant appears in some minimal authorized coalition. -/
def EssentialShare (A : TropicalAccessPresentation P) (p : P) : Prop :=
  ∃ C : Finset P, MinimalAuthorized A C ∧ p ∈ C


/-- **Reconstruction Equivalence**: same authorized coalitions. -/
def ReconstructionEquivalent (A B : TropicalAccessPresentation P) : Prop :=
  ∀ C : Finset P, Authorized A C ↔ Authorized B C

/-! ## §2. Monotonicity and Basic Properties -/









/-! ## §3. Extremal Attainment = Minimal Authorization -/




/-! ## §4. Theorem 1: Realization Theorem -/


/-! ## §5. Blocker-Characterized Access Structures

The key insight: tropical access presentations with ∀-dimensional authorization
naturally encode **blocker-type** structures. A coalition is authorized iff it
**intersects** every member of a blocking family (the Alexander dual).

This is the correct bridge between:
- tropical geometry (where authorization is threshold attainment in ALL coordinates)
- cryptographic access structures (where authorization is inclusion of SOME minimal set) -/

/-- A blocker-characterized access structure: authorization iff the coalition
    intersects every blocking set. This is the Alexander dual formulation. -/
structure BlockerAccessStructure (P : Type*) [Fintype P] [DecidableEq P] where
  /-- Number of blocking sets -/
  numBlock : ℕ
  numBlock_pos : 0 < numBlock
  /-- The blocking sets -/
  blockSet : Fin numBlock → Finset P
  /-- Each blocking set is nonempty -/
  blockSet_nonempty : ∀ i, (blockSet i).Nonempty

/-- The authorization predicate for a blocker access structure:
    C is authorized iff C intersects every blocking set. -/
def BlockerAccessStructure.auth (Γ : BlockerAccessStructure P) (C : Finset P) : Prop :=
  ∀ i : Fin Γ.numBlock, (C ∩ Γ.blockSet i).Nonempty

instance (Γ : BlockerAccessStructure P) (C : Finset P) :
    Decidable (Γ.auth C) :=
  Fintype.decidableForallFintype



/-! ## §6. Canonical Construction from Blockers -/

/-- **Canonical Tropical Presentation from Blockers**:
    - Column j corresponds to blocking set B_j
    - mat(p, j) = 1 if p ∈ B_j, 0 otherwise
    - Threshold = 1 in all dimensions
    - Authorized C ↔ C intersects every blocking set ↔ Γ.auth C -/
def canonicalPresentation (Γ : BlockerAccessStructure P) :
    TropicalAccessPresentation P where
  genDim := Γ.numBlock
  genDim_pos := Γ.numBlock_pos
  mat := fun p j => if p ∈ Γ.blockSet j then 1 else 0
  thresh := fun _ => 1
  thresh_pos := fun _ => Nat.one_pos

/-
Score at column j is 1 iff C intersects blocking set j.
-/

/-
Score at column j ≥ 1 iff C intersects blocking set j.
-/

/-
**Canonical presentation is correct**: authorizes exactly the blocker structure.
-/

/-! ## §7. Theorem 2: Reconstruction Theorem -/


/-
**Canonical presentation is irredundant**: each column is essential.
-/

/-! ## §8. Tropical Semimodule Isomorphism -/

/-- **Tropical Access Semimodule**: packages algebraic data for isomorphism comparison. -/
structure TropicalAccessSemimodule (P : Type*) [Fintype P] [DecidableEq P] where
  dim : ℕ
  generators : P → Fin dim → ℕ
  threshold : Fin dim → ℕ

/-- Extract the access semimodule from a presentation. -/
def TropicalAccessPresentation.toSemimodule (A : TropicalAccessPresentation P) :
    TropicalAccessSemimodule P where
  dim := A.genDim
  generators := A.mat
  threshold := A.thresh

/-- **Tropical Semimodule Isomorphism**: dimension bijection preserving
    generators and threshold. -/
structure TropicalSemimoduleIso (M₁ M₂ : TropicalAccessSemimodule P) where
  dimEquiv : Fin M₁.dim ≃ Fin M₂.dim
  gen_compat : ∀ (p : P) (j : Fin M₁.dim), M₁.generators p j = M₂.generators p (dimEquiv j)
  thresh_compat : ∀ (j : Fin M₁.dim), M₁.threshold j = M₂.threshold (dimEquiv j)

/-
**Isomorphic semimodules authorize the same coalitions.**
-/




/-! ## §9. Theorem 3: Duality — Forward Direction -/


/-! ## §10. Well-Foundedness and Minimality -/



/-
**Any authorized set contains a minimal authorized subset.**
-/

/-! ## §11. Tropical Closure Infrastructure -/

/-- **Tropical closure**: all participants dominated by a coalition's score. -/
def tropicalClosure (A : TropicalAccessPresentation P) (C : Finset P) : Finset P :=
  Finset.univ.filter (fun p => ∀ j : Fin A.genDim, A.mat p j ≤ coalitionScore A C j)



/-! ## §12. Concrete Example: (2,3)-Threshold Scheme -/

/-- **Threshold-2-of-3 scheme**: Three participants; any two can reconstruct.
    This is realized by the blocker construction: the blockers are the 2-element subsets
    (equivalently, the complements of singletons, but for (2,3)-threshold the blockers
    equal the minimal authorized sets).

    Alternatively, as a direct tropical construction: each column excludes one participant,
    so authorization requires coverage in all three exclusion dimensions. -/
def threshold_2_of_3 : TropicalAccessPresentation (Fin 3) where
  genDim := 3
  genDim_pos := by omega
  mat := fun p j => if p.val ≠ j.val then 1 else 0
  thresh := fun _ => 1
  thresh_pos := fun _ => by omega

/-
The (2,3)-threshold scheme authorizes any pair.
-/

/-
The (2,3)-threshold scheme does not authorize singletons.
-/

/-
Pairs are minimal authorized in the (2,3)-threshold scheme.
-/

/-! ## §13. Score Composition Lemmas -/



/-! ## §14. Canonical GenDim -/


/-! ## §15. Summary Package -/



end TropicalSecretSharing


