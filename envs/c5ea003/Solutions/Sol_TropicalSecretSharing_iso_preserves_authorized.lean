-- Prove2me | solution 1 for TropicalSecretSharing.iso_preserves_authorized
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:33.087494+00:00
-- url     : https://prove2.me/submissions/b52ec1ba-a80f-4737-8bb1-a84b59fac721

-- Sol generated from Bridges/TropicalValuationSecretSharingDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalValuationSecretSharingDuality
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

open TropicalSecretSharing

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ## §1. Core Definitions -/










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






/-! ## §6. Canonical Construction from Blockers -/


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




/-
**Isomorphic semimodules authorize the same coalitions.**
-/




/-! ## §9. Theorem 3: Duality — Forward Direction -/


/-! ## §10. Well-Foundedness and Minimality -/



/-
**Any authorized set contains a minimal authorized subset.**
-/

/-! ## §11. Tropical Closure Infrastructure -/




/-! ## §12. Concrete Example: (2,3)-Threshold Scheme -/


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




open TropicalSecretSharing in
theorem solution    (A B : TropicalAccessPresentation P)
    (iso : TropicalSemimoduleIso A.toSemimodule B.toSemimodule) :
    ReconstructionEquivalent A B := by
  intro C
  constructor
  intro hA
  generalize_proofs at *; (
  intro j
  generalize_proofs at *; (
  obtain ⟨ j', hj' ⟩ := iso.dimEquiv.surjective j; specialize hA j'; simp_all +decide [ coalitionScore ] ;
  have := iso.thresh_compat j'; have := iso.gen_compat; simp_all +decide [ TropicalAccessPresentation.toSemimodule ] ;));
  intro hC j;
  convert hC ( iso.dimEquiv j ) using 1;
  · exact iso.thresh_compat j;
  · exact Finset.sup_congr rfl fun p hp => iso.gen_compat p j
