-- Prove2me | Theorems.Thm_mme_recursive_yz_profiled_repaired_CW_extraction
-- name    : mme_recursive_yz_profiled_repaired_CW_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T14:42:02.945981+00:00
-- url     : https://prove2.me/theorems/64845d62-b63e-4529-971d-072943fece97
-- title:
--   Repaired CW copies from a parent-profiled source
-- statement:
--   For k distinct target-type recursive CW addresses satisfying the explicit hashing and isolation hypotheses, let the bad words in each mode be the union of the previous Y/Z ownership holes and all words rejected by the parent fine-profile predicate. Assume each such union has at most 1/(4d) of its mode words, and the product of the three template word-set sizes is less than d^h. Then the actual parent-projected CW power restricts to floor(k/8^h) independent intact exact-profile child interfaces. All three parent-profile losses, including X, are counted. This finite theorem does not assert the hole-density bounds or their asymptotic entropy estimates.
-- source:
--   Finite algebraic ingredients for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3, Theorem 6.4, and Sections 6.5–6.6. These statements retain explicit finite hole budgets and type-copy overheads; they do not assert the entropy asymptotics or numerical certificate.

import Theorems.Thm_mme_bigAdd_fin_mul_grouped_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_recursive_yz_actual_CW_cell_finite_hole_repair
import Theorems.Thm_mme_recursive_yz_profiled_CW_ownership_extraction
import Theorems.Thm_mme_recursive_yz_same_type_cell_permutation
import Theorems.Thm_mme_recursive_yz_nonhole_implies_owned
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Definitions.Def_mme_recursive_yz_CW_cells
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_modern_three_mode_projected_tensor
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.DWZComponentRestriction MME.ModernRepair Module
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v w

theorem mme_recursive_yz_profiled_repaired_CW_extraction {K : Type u} [Field K] (q ell half R N p L d h k : ℕ)
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (positions : Fin L ≃ Position n)
    (S : Finset (ZMod p)) (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m)
    (address : Fin k → Address half R parent n) (hinj : Function.Injective address)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hE : ∀ j, address j ∈ RecursiveXHash.bucketed m e S state)
    (hHash : ∀ j, address j ∈ RecursiveXHash.hashed m e S state)
    (hiso : ∀ j b, b ∈ RecursiveXHash.bucketed m e S state →
      RecursiveXHash.block 0 (address j) = RecursiveXHash.block 0 b → address j = b)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) (hmu : BoundaryProfiles mu)
    (keep : Fin 2 → Fin k → (Position n → CompleteWord ell) → Prop)
    (parentKeep : Fin 3 → (Position n → CompleteWord ell) → Prop)
    (hholes : ∀ j (i : Fin 3), 4 * d *
      ((unbrokenWords htotal i (address j) (mu i)).filter (fun f ↦ ¬ parentKeep i f) ∪
        (if i = 1 then filterHoles htotal m e S state 0 (mu 1) (address j) (keep 0 j)
         else if i = 2 then filterHoles htotal m e S state 1 (mu 2) (address j) (keep 1 j)
         else ∅)).card ≤ (unbrokenWords htotal i (address j) (mu i)).card)
    (hcapacity : (∏ i : Fin 3, Nat.card (Block ell (fullCell htotal ref)
      (fun c i ↦ (c.2.val i).val) mu i)) < d ^ h) :
    Restrict (bigAdd (fun _ : Fin (k / 8 ^ h) ↦
      unbroken K q ell L positions (fullCell htotal ref) (fun c i ↦ (c.2.val i).val) mu))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun i x ↦ parentKeep i (CWCells.label q ell L positions x))) := by sorry
