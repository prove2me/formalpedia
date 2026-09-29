-- Prove2me | Theorems.Thm_mme_recursive_yz_profiled_CW_ownership_extraction
-- name    : mme_recursive_yz_profiled_CW_ownership_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:29:07.281727+00:00
-- url     : https://prove2.me/theorems/aed9e936-5f8b-49c6-9b2e-803409c4bf27
-- title:
--   CW ownership extraction preserves imposed parent profiles
-- statement:
--   For actual CW tensor powers and a target-type family of hashed recursive addresses with isolated X blocks, impose the proved sequential Y/Z ownership filters together with any fixed parent fine-word predicate in all three modes. The direct sum of the resulting owned, parent-restricted tensors is an actual restriction of the parent-projected CW power. The boundary profile identities, fine CW support, and hash isolation hypotheses are explicit. No extraction map or source-profile preservation is assumed.
-- source:
--   Finite projected-source algebra for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.2–6.5, especially Proposition 6.3. https://arxiv.org/html/2404.16349v2#S6 . The arbitrary parent predicate and explicit finite hypotheses are an adapter for the recursive source; this is not the full asymptotic proposition.

import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_recursive_x_hash_families
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_modern_CW_full_word_boundary_histograms
import Theorems.Thm_mme_CW_three_canonical_support
import Theorems.Thm_mme_modern_CW_power_nonzero_coefficient_fine_support
import Theorems.Thm_mme_basis_projected_family_restrict

open BigOperators MME MME.CompleteSplit MME.DWZStep1Support MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
universe u

open Module MME.TensorObj

theorem mme_recursive_yz_profiled_CW_ownership_extraction {K : Type u} [Field K] (q ell half R k N p L : ℕ)
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (positions : Fin L ≃ Position n)
    (S : Finset (ZMod p)) (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (address : Fin k → Address half R parent n)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hE : ∀ j, address j ∈ RecursiveXHash.bucketed m e S state)
    (hiso : ∀ j b, b ∈ RecursiveXHash.bucketed m e S state →
      RecursiveXHash.block 0 (address j) = RecursiveXHash.block 0 b → address j = b)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (hmu : BoundaryProfiles mu)
    (parentKeep : Fin 3 → (Position n → CompleteWord ell) → Prop) :
    let T := (CWObj K q).kronPow (L * 2 ^ (ell - 1))
    let b := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (L * 2 ^ (ell - 1))
    let label := fun (w : Fin (L * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
      (p : Position n) (r : Fin (2 ^ (ell - 1))) ↦
        cwSquareCoordGrade q (w (finProdFinEquiv (positions.symm p, r))).down
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦ T.basisAllAllowedSubtensor b
        (fun i x ↦ Owned htotal address mu j i (label x) ∧ parentKeep i (label x))))
      (T.basisAllAllowedSubtensor b (fun i x ↦ parentKeep i (label x))) := by sorry
