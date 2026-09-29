-- Prove2me | Theorems.Thm_mme_recursive_yz_actual_CW_power_extraction
-- name    : mme_recursive_yz_actual_CW_power_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T10:20:13.828236+00:00
-- url     : https://prove2.me/theorems/b76184dc-35c9-400d-9c13-61f015c04ce7
-- title:
--   Recursive Y/Z filtering: actual direct-sum extraction from a CW power
-- statement:
--   Let the recursive child grade be $h=2\cdot2^{\ell-1}$, with parent grades totaling $2h$. Choose exact-profile recursive addresses in a common coordinate-hash bucket. Suppose each chosen X word belongs to exactly one address throughout the entire retained ambient bucket. Let $L$ count all physical child positions, including both halves of every parent occurrence.
--
--   Fix full fine-word profiles satisfying the three CW boundary identities. At each chosen address retain coordinate words satisfying its actual child grades, its exact fine-cell profiles, and unique Y/Z compatibility among the chosen addresses. Then the direct sum of these coordinate-filtered tensors is an actual restriction of
--
--   $$CW_q^{\otimes L2^{\ell-1}}$$
--
--   over every field.
--
--   The source, its bases, and its fine labels are the literal canonical CW tensor power. No ownership or nonzero-coefficient compatibility theorem is assumed. The extracted copies may have holes caused by the ownership filters; this theorem establishes their independence, not their subsequent repair or any asymptotic copy-count estimate.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.2--6.4; https://arxiv.org/html/2404.16349v2. Exact finite tensor-level formulation of the independent-copy filtering step.

import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_recursive_x_hash_families
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
open BigOperators MME MME.CompleteSplit MME.DWZStep1Support MME.RecursiveYZ Module MME.TensorObj
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_recursive_yz_actual_CW_power_extraction {K : Type u} [Field K] (q ell half R k N p L : ℕ)
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
    (hmu : BoundaryProfiles mu) :
    let T := (CWObj K q).kronPow (L * 2 ^ (ell - 1))
    let b := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (L * 2 ^ (ell - 1))
    let label := fun (w : Fin (L * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
      (p : Position n) (r : Fin (2 ^ (ell - 1))) ↦
        cwSquareCoordGrade q (w (finProdFinEquiv (positions.symm p, r))).down
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦ T.basisAllAllowedSubtensor b
        (fun i x ↦ Owned htotal address mu j i (label x)))) T := by sorry
